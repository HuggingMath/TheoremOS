#!/usr/bin/env python3
"""Build the evaluation inventory from the published evidence files."""

import argparse
import csv
import hashlib
import io
import json
import re
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path


OBSERVATIONS = "data/evaluation/selected-run-observations.json"
STATUSES = {"official_accepted", "locally_verified", "in_progress_not_officially_accepted"}
LIMITS = (
    "maxRunSeconds", "maxTurns", "maxTurnSeconds", "maxTotalTokens",
    "evaluatorTimeoutSeconds",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def duration_seconds(run):
    if not run.get("startedAt") or not run.get("finishedAt"):
        return None
    start = datetime.fromisoformat(run["startedAt"].replace("Z", "+00:00"))
    finish = datetime.fromisoformat(run["finishedAt"].replace("Z", "+00:00"))
    duration = round((finish - start).total_seconds(), 3)
    require(duration >= 0, f"Negative recorded duration: {run['runId']}")
    return duration


def csv_text(rows, fields):
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def build_snapshot(root):
    sources = {}

    def read_bytes(relative):
        path = root / relative
        require(path.is_file(), f"Missing input: {relative}")
        content = path.read_bytes()
        sources[relative] = {
            "path": relative,
            "sha256": hashlib.sha256(content).hexdigest(),
        }
        return content

    def read_json(relative):
        return json.loads(read_bytes(relative))

    def check_hash(relative, expected):
        read_bytes(relative)
        require(sources[relative]["sha256"] == expected, f"SHA-256 mismatch: {relative}")

    catalog = read_json("data/catalog.json")
    accepted = read_json("accepted/accepted.json")
    submitted = read_json("submitted/submitted.json")
    official_result = read_json("submitted/official-results.json")
    require(
        sources["submitted/submitted.json"]["sha256"]
        == official_result["submission_manifest_sha256"],
        "Official result does not bind the submitted manifest",
    )

    official = {}
    for item in accepted:
        require(item["status"] == "official_accepted", "Unexpected accepted-index status")
        require(item["problem_id"] not in official, "Duplicate accepted problem")
        official[item["problem_id"]] = (item, "accepted", item["result_url"])
    submitted_by_id = {item["problem_id"]: item for item in submitted}
    require(len(submitted_by_id) == len(submitted), "Duplicate submitted problem")
    for result in official_result["problems"]:
        item = submitted_by_id.get(result["problem_id"])
        require(item is not None, f"Official result has no submission: {result['problem_id']}")
        require(
            result["status"] == "official_accepted"
            and item["statement_revision"] == result["statement_revision"]
            and item["submission_url"] == official_result["submission_url"],
            f"Official result identity mismatch: {result['problem_id']}",
        )
        require(result["problem_id"] not in official, "Duplicate official problem")
        official[result["problem_id"]] = (item, "submitted", official_result["result_url"])

    observed = read_json(OBSERVATIONS)
    require(observed["schema"] == "theoremos.selected-run-observations.v1", "Unknown observation schema")
    observations = {item["publicId"]: item for item in observed["observations"]}
    require(len(observations) == len(observed["observations"]), "Duplicate metering observation")
    records, runs, seen_ids, seen_runs, used_observations = [], [], set(), set(), set()

    for index, record in enumerate(catalog["records"]):
        identity = record["id"]
        require(identity not in seen_ids, f"Duplicate catalog record: {identity}")
        require(record["status"] in STATUSES, f"Unknown catalog status: {identity}")
        seen_ids.add(identity)
        row = {
            "id": identity,
            "title": record["title"],
            "titleZh": record["subtitle"],
            "status": record["status"],
            "modelLabel": record["model"],
            "modelLabelSource": f"data/catalog.json#/records/{index}/model",
            "selectedRunId": None,
            "selectedRunDurationSeconds": None,
            "selectedRunTurns": None,
            "selectedRunWorkers": None,
            "reportedUsage": None,
            "usageComplete": None,
            "recordedLaunchBudget": None,
            "tokenBudget": None,
            "costUsd": None,
            "recordedRunCount": None,
            "targetNames": None,
            "officialResultUrl": None,
            "verificationSource": None,
            "processSource": None,
            "observationSource": None,
        }

        if record["status"] == "official_accepted":
            require(identity in official, f"Missing official result: {identity}")
            item, directory, result_url = official[identity]
            require(
                record["official"]["resultUrl"] == result_url
                and record["official"]["statementRevision"] == item["statement_revision"]
                and record["model"] == item["model"],
                f"Catalog official identity mismatch: {identity}",
            )
            for name, expected in item["source_sha256"].items():
                check_hash(f"{directory}/{item['directory']}/{name}", expected)
            row.update({
                "officialResultUrl": result_url,
                "statementRevision": item["statement_revision"],
                "originalSourceCommit": item["original_source_commit"],
            })
        elif record["status"] == "locally_verified":
            base = f"data/proofs/{identity}"
            verification_path = f"{base}/verification.json"
            process_path = f"{base}/process.json"
            verification = read_json(verification_path)
            process = read_json(process_path)
            require(
                verification["status"] == "evaluated_passed"
                and verification["kernelStatus"] == "kernel_verified"
                and verification["comparatorExitCode"] == 0
                and verification["reviewStatus"] == "accepted",
                f"Non-passing verification: {identity}",
            )
            for key in ("runId", "proofCommit", "proofSha256", "targets"):
                require(record["campaign"][key] == verification[key], f"Catalog verification mismatch: {identity}/{key}")
            check_hash(f"{base}/Submission.lean", verification["proofSha256"])
            selected = None
            for run_index, run in enumerate(process["runs"]):
                require(run["runId"] not in seen_runs, f"Duplicate recorded run: {run['runId']}")
                seen_runs.add(run["runId"])
                is_selected = run["runId"] == verification["runId"]
                duration = duration_seconds(run)
                run_row = {
                    "recordId": identity,
                    "runId": run["runId"],
                    "resultStatus": run.get("resultStatus"),
                    "phase": run.get("phase"),
                    "startedAt": run.get("startedAt"),
                    "finishedAt": run.get("finishedAt"),
                    "recordedDurationSeconds": duration,
                    "turns": run.get("turns"),
                    "workers": run.get("workers"),
                    "selectedForPublishedVerification": is_selected,
                    "source": f"{process_path}#/runs/{run_index}",
                }
                runs.append(run_row)
                if is_selected:
                    selected = run_row
            require(selected is not None, f"Verification runId missing from process: {identity}")
            require(selected["resultStatus"] == "evaluated_passed", f"Selected run did not pass: {identity}")
            observation = observations.get(identity)
            require(observation is not None, f"Missing selected-run observation: {identity}")
            require(
                observation["runId"] == verification["runId"]
                and observation["solutionCommit"] == verification["proofCommit"]
                and observation["proofSha256"] == verification["proofSha256"],
                f"Observation proof/run binding mismatch: {identity}",
            )
            for digest in (observation["rawResultSha256"], observation["configurationEvidence"]["launchSha256"]):
                require(bool(re.fullmatch(r"[0-9a-f]{64}", digest)), f"Invalid observation source hash: {identity}")
            require(all(observation["binding"].values()), f"Unestablished observation binding: {identity}")
            require(
                selected["recordedDurationSeconds"] is not None
                and observation["solveWallMs"] == round(selected["recordedDurationSeconds"] * 1000),
                f"Observation duration mismatch: {identity}",
            )
            usage = observation["reportedUsage"]
            require(
                all(type(usage[key]) is int and usage[key] >= 0 for key in ("inputTokens", "outputTokens", "totalTokens"))
                and usage["inputTokens"] + usage["outputTokens"] == usage["totalTokens"],
                f"Inconsistent reported token counters: {identity}",
            )
            token_budget = observation["tokenBudget"]
            require(
                type(observation["usageComplete"]) is bool
                and token_budget["usageComplete"] == observation["usageComplete"]
                and token_budget["reportedTotalTokens"] == usage["totalTokens"],
                f"Inconsistent token completeness/counter: {identity}",
            )
            evidence = observation["configurationEvidence"]
            launch_budget = observation["recordedLaunchBudget"]
            require(
                evidence["outputMatchesResult"] is True
                and evidence["targetMatches"] is True
                and evidence["sameRunConfigurationEstablished"] is True
                and all(type(launch_budget[key]) is int and launch_budget[key] >= 0 for key in LIMITS)
                and launch_budget["maxTotalTokens"] == token_budget["maxTotalTokens"],
                f"Unestablished launch budget: {identity}",
            )
            used_observations.add(identity)
            row.update({
                "selectedRunId": selected["runId"],
                "selectedRunDurationSeconds": selected["recordedDurationSeconds"],
                "selectedRunStartedAt": selected["startedAt"],
                "selectedRunFinishedAt": selected["finishedAt"],
                "selectedRunTurns": selected["turns"],
                "selectedRunWorkers": selected["workers"],
                "reportedUsage": usage,
                "usageComplete": observation["usageComplete"],
                "recordedLaunchBudget": launch_budget,
                "tokenBudget": token_budget,
                "reportedSolveWallMs": observation["solveWallMs"],
                "rawResultSha256": observation["rawResultSha256"],
                "rawLaunchSha256": evidence["launchSha256"],
                "recordedRunCount": len(process["runs"]),
                "recordedRunStatusCounts": dict(sorted(Counter(run.get("resultStatus") for run in process["runs"]).items())),
                "targetNames": verification["targets"],
                "verificationSource": verification_path,
                "processSource": process_path,
                "selectedRunSource": selected["source"],
                "observationSource": f"{OBSERVATIONS}#/observations/{observed['observations'].index(observation)}",
                "attribution": verification.get("attributionEn"),
                "verification": {key: verification[key] for key in (
                    "status", "kernelStatus", "comparatorExitCode", "reviewStatus", "proofCommit", "proofSha256",
                )},
            })
        else:
            row["snapshot"] = record.get("snapshot")
        records.append(row)

    require(used_observations == set(observations), "Observation has no matching published verified record")
    require({row["id"] for row in records if row["status"] == "official_accepted"} == set(official), "Catalog/official index coverage mismatch")
    records.sort(key=lambda row: row["id"])
    runs.sort(key=lambda row: (row["recordId"], row["startedAt"] or "", row["runId"]))
    counts = Counter(row["status"] for row in records)
    snapshot = {
        "schema": "theoremos.evaluation-snapshot.v1",
        "scope": "Published archive inventory and selected-run observations; not a fixed-cohort benchmark.",
        "archiveSnapshotAt": catalog["snapshotAt"],
        "archiveRevision": catalog["archiveRevision"],
        "counts": {
            "archiveRecords": len(records),
            "passingRecords": counts["official_accepted"] + counts["locally_verified"],
            "officialLeanEvalPasses": counts["official_accepted"],
            "projectLeanComparatorPasses": counts["locally_verified"],
            "unfinishedResearchSnapshots": counts["in_progress_not_officially_accepted"],
            "openAiRecordTargetDeclarations": sum(len(row["targetNames"] or []) for row in records),
            "publicProcessRuns": len(runs),
            "publicRunsWithTimestampPairs": sum(run["recordedDurationSeconds"] is not None for run in runs),
            "publicRunStatusCounts": dict(sorted(Counter(run["resultStatus"] for run in runs).items())),
            "selectedRunMeteringObservations": len(used_observations),
            "selectedRunUsageMarkedComplete": sum(row["usageComplete"] is True for row in records),
            "selectedRunUsageMarkedIncomplete": sum(row["usageComplete"] is False for row in records),
        },
        "comparisonMetrics": {
            "fixedCohortDenominator": None,
            "successRate": None,
            "fromScratchTime": None,
            "fullTokenUsage": None,
            "totalCostUsd": None,
        },
        "definitions": {
            "archiveRecord": "One catalog entry with its own statement and provenance. Entries may contain several targets or support/conditional results.",
            "selection": "The 16 project-verified records were selected for publication after passing. Their 45 saved runs are histories of those selected problems, not an evaluation denominator.",
            "projectVerification": "The recorded Lean kernel and original comparator passed; OpenAI-hosted evaluation remains unconfirmed.",
            "modelLabel": "The original catalog label, not an independently reconstructed per-call model history.",
            "selectedRunDurationSeconds": "finishedAt minus startedAt for verification.runId. This is a saved interval for that run, not from-scratch or total proof-production time.",
            "reportedUsage": "The exact counters stored on the selected result, supplied by the source observations. These are not complete proof-production totals. usageComplete describes this run's recorded metering only.",
            "recordedLaunchBudget": "The saved launch limits for the selected result. A value of zero means unlimited. These are not common limits across all attempts or continuations.",
            "sourceHashes": "Public source-file hashes are recomputed here. Original result/launch hashes identify privately retained source artifacts inspected for the observations; this script does not independently reproduce their counters.",
            "unfinishedSnapshot": "A historical saved research state. Its phase and turn count do not describe a currently live run.",
            "null": "Not established for this scope. Null is not zero usage, zero cost, or an unlimited budget. CSV represents null with an empty cell.",
        },
        "fieldProvenance": {
            "identityStatusModel": "data/catalog.json#/records",
            "officialPasses": "accepted/accepted.json plus submitted/official-results.json, bound to submitted/submitted.json by submission_manifest_sha256",
            "projectVerification": "data/proofs/{id}/verification.json and the matching Submission.lean SHA-256",
            "runs": "data/proofs/{id}/process.json; the selected run is matched by verification.runId",
            "usageAndLaunchLimits": OBSERVATIONS,
        },
        "records": records,
        "runs": runs,
        "sourceFiles": [sources[key] for key in sorted(sources)],
    }
    flat_records = []
    for row in records:
        usage, budget = row["reportedUsage"] or {}, row["recordedLaunchBudget"] or {}
        flat_records.append({
            **{key: row.get(key) for key in (
                "id", "title", "status", "modelLabel", "selectedRunId", "selectedRunDurationSeconds",
                "selectedRunTurns", "selectedRunWorkers", "usageComplete", "costUsd", "officialResultUrl",
                "verificationSource", "processSource", "rawResultSha256",
            )},
            "reportedInputTokens": usage.get("inputTokens"),
            "reportedOutputTokens": usage.get("outputTokens"),
            "reportedTotalTokens": usage.get("totalTokens"),
            **{f"recorded{key[0].upper()}{key[1:]}": budget.get(key) for key in LIMITS},
        })
    record_fields = list(flat_records[0]) if flat_records else ["id"]
    run_fields = list(runs[0]) if runs else ["recordId", "runId"]
    return {
        "snapshot.json": json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n",
        "records.csv": csv_text(flat_records, record_fields),
        "runs.csv": csv_text(runs, run_fields),
    }, snapshot["counts"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--check", action="store_true", help="Verify generated files without writing them")
    args = parser.parse_args()
    try:
        outputs, counts = build_snapshot(args.root.resolve())
        directory = args.root / "data/evaluation"
        if args.check:
            stale = [name for name, content in outputs.items() if not (directory / name).is_file()
                     or (directory / name).read_bytes() != content.encode("utf-8")]
            require(not stale, "Generated evaluation files are missing or stale: " + ", ".join(stale))
        else:
            directory.mkdir(parents=True, exist_ok=True)
            for name, content in outputs.items():
                (directory / name).write_text(content, encoding="utf-8")
        print(("Checked" if args.check else "Wrote") + " evaluation snapshot: "
              + f"{counts['archiveRecords']} records, {counts['passingRecords']} passing, "
              + f"{counts['publicProcessRuns']} recorded runs")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Evaluation snapshot error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
