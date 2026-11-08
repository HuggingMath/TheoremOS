#!/usr/bin/env python3
"""Check the frozen Dimitrov proof with Lean and the original comparator."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "verification-output"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_files():
    entries = []
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, name = line.split("  ", 1)
        path = ROOT / name
        if not path.is_file() or sha256(path) != expected:
            raise RuntimeError(f"File checksum mismatch or missing file: {name}")
        entries.append({"path": name, "sha256": expected})
    print(f"PASS: {len(entries)} file checksums", flush=True)
    return entries


def run(command, label, report):
    started = time.monotonic()
    print("Running: " + " ".join(command), flush=True)
    stdout_path = OUTPUT / f"{label}.stdout.log"
    stderr_path = OUTPUT / f"{label}.stderr.log"
    with stdout_path.open("w") as stdout, stderr_path.open("w") as stderr:
        result = subprocess.run(command, cwd=ROOT, stdout=stdout, stderr=stderr)
    report["commands"].append({
        "command": command,
        "exitCode": result.returncode,
        "durationSeconds": round(time.monotonic() - started, 3),
        "stdout": stdout_path.name,
        "stdoutSha256": sha256(stdout_path),
        "stderr": stderr_path.name,
        "stderrSha256": sha256(stderr_path),
    })
    if result.returncode:
        print(stderr_path.read_text(errors="replace")[-6000:], file=sys.stderr)
        print(stdout_path.read_text(errors="replace")[-6000:], file=sys.stderr)
        raise RuntimeError(f"{label} failed; see verification-output/{label}.*.log")
    return stdout_path.read_text(errors="replace")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true", help="Install the pinned Lean toolchain and fetch Lake dependencies and Mathlib cache first.")
    parser.add_argument("--lean-only", action="store_true", help="Compile and inspect axioms without running the original comparator or nanoda.")
    parser.add_argument("--check-files", action="store_true", help="Only check the packaged files; no downloads or Lean execution.")
    args = parser.parse_args()
    os.chdir(ROOT)
    OUTPUT.mkdir(exist_ok=True)
    report = {
        "schema": "theoremos.proof-kit-verification.v1",
        "checkedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "problemId": "dimitrov",
        "scope": "files-only" if args.check_files else "lean-only" if args.lean_only else "lean-and-original-comparator",
        "status": "failed",
        "commands": [],
        "checks": {"files": False, "leanBuild": False, "axioms": False, "originalComparatorWithNanoda": False},
    }
    try:
        report["files"] = check_files()
        report["checks"]["files"] = True
        if args.check_files:
            report["status"] = "passed"
            return 0

        for executable in (["elan", "lake", "git"] if args.prepare else ["lake", "git"]):
            if not shutil.which(executable):
                raise RuntimeError(f"Missing {executable}; install Elan/Git and put their binaries on PATH.")

        source = json.loads((ROOT / "sources.json").read_text())
        if args.prepare:
            run(["elan", "toolchain", "install", source["environment"]["lean"]], "toolchain-install", report)
            run(["lake", "exe", "cache", "get"], "mathlib-cache", report)
            check_files()

        lean_version = run(["lake", "env", "lean", "--version"], "lean-version", report).strip()
        if "version 4.35.0-rc3" not in lean_version:
            raise RuntimeError(f"Unexpected Lean version: {lean_version}")
        mathlib_revision = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], "mathlib-revision", report).strip()
        if mathlib_revision != source["environment"]["mathlib"]:
            raise RuntimeError(f"Unexpected Mathlib revision: {mathlib_revision}")
        report["environment"] = {"leanVersion": lean_version, "mathlibRevision": mathlib_revision}

        run(["lake", "build", "Submission", "Solution"], "lean-build", report)
        report["checks"]["leanBuild"] = True
        axioms_output = run(["lake", "env", "lean", "Check.lean"], "axioms", report)
        match = re.search(r"'Submission\.dimitrov' depends on axioms:\s*\[([^\]]*)\]", axioms_output)
        if match:
            axioms = sorted(item.strip() for item in match.group(1).split(",") if item.strip())
        elif "'Submission.dimitrov' does not depend on any axioms" in axioms_output:
            axioms = []
        else:
            raise RuntimeError("Could not read the theorem's axiom list from Lean output.")
        permitted = {"propext", "Quot.sound", "Classical.choice"}
        if set(axioms) - permitted:
            raise RuntimeError("The proof depends on unpermitted axioms: " + ", ".join(set(axioms) - permitted))
        report["axioms"] = axioms
        report["checks"]["axioms"] = True

        if not args.lean_only:
            run(["lake", "test"], "comparator", report)
            report["checks"]["originalComparatorWithNanoda"] = True
        report["status"] = "passed"
        print("PASS: " + report["scope"], flush=True)
        return 0
    except (OSError, RuntimeError, ValueError) as error:
        report["error"] = str(error)
        print(str(error), file=sys.stderr)
        return 1
    finally:
        report["finishedAt"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print("Report: verification-output/report.json", flush=True)


if __name__ == "__main__":
    sys.exit(main())
