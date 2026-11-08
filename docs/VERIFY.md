# Verify a published proof

[简体中文](VERIFY.zh-CN.md) · [TheoremOS](../README.md)

The public proof packages can be checked with Lean and the original benchmark tools. No TheoremOS account, private runtime, or model API key is required.

## Quick check: the website replay example

Install Git, Python 3, and [Elan / Lean](https://lean-lang.org/install/). The [short example](../examples/lean-check/Submission.lean) proves the two statements shown in the [website's preset replay](https://theoremos.top/en/#demo), `Tutorial.add_zero` and `Tutorial.zero_add`, using only Lean's standard library:

```bash
git clone https://github.com/LikC1606/TheoremOS.git
cd TheoremOS
elan toolchain install leanprover/lean4:v4.33.0
lean +leanprover/lean4:v4.33.0 examples/lean-check/Submission.lean
```

The command should exit successfully and print that each theorem does not depend on any axioms. This example demonstrates the checking workflow without Mathlib or model calls; the research proof records below have their own statements and environments.

## Dimitrov: reproduce an archived proof

This walkthrough uses [Dimitrov's lower bound](../accepted/dimitrov/), which has an [official Lean-Eval passing result](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969). Its archived environment fixes:

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22` |
| Original Lean-Eval workspace | `38361be884302c7edce1908c4aef8296eb2cb27e` |
| Submitted theorem | `Submission.dimitrov` |

### 1. Check the archived files

From the public repository cloned above:

```bash
git rev-parse HEAD

python3 - <<'PY'
from pathlib import Path
import hashlib
import json

records = json.loads(Path('accepted/accepted.json').read_text())
record = next(item for item in records if item['problem_id'] == 'dimitrov')
package = Path('accepted') / record['directory']
for relative_path, expected in record['source_sha256'].items():
    actual = hashlib.sha256((package / relative_path).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'Hash mismatch: {relative_path}')
    print(f'PASS {relative_path}')
PY
```

Keep the printed repository commit with your results. The hash check identifies the archived proof and environment files; it does not run Lean.

### 2. Restore the original benchmark workspace

The archive contains the submitted proof files, rather than the complete benchmark workspace. Obtain the fixed challenge, solution bridge, and test harness from the recorded Lean-Eval revision:

```bash
cd ..
git clone https://github.com/leanprover/lean-eval.git
git -C lean-eval checkout 38361be884302c7edce1908c4aef8296eb2cb27e

cp -R lean-eval/generated/dimitrov verify-dimitrov
cp TheoremOS/accepted/dimitrov/Submission.lean verify-dimitrov/Submission.lean
cp -R TheoremOS/accepted/dimitrov/Submission/. verify-dimitrov/Submission/
cp TheoremOS/accepted/dimitrov/lake-manifest.json verify-dimitrov/lake-manifest.json
```

Keep `Challenge.lean`, `Solution.lean`, `WorkspaceTest.lean`, `config.json`, `lakefile.toml`, and `lean-toolchain` from that frozen workspace. The archived `lakefile.toml` and `lean-toolchain` match it byte for byte; the copied manifest pins the archived dependency revisions.

### 3. Compile the submitted proof

The first setup downloads the pinned Lean toolchain, Mathlib dependencies, and compiled Mathlib cache. Existing compatible caches can be reused.

```bash
cd verify-dimitrov
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake update
lake exe cache get

lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
lake build Submission
```

The reported Lean version should be `4.35.0-rc3`, and Mathlib should be at the revision listed above. A successful `lake build Submission` checks the submitted declaration and its helper proofs in Lean.

### 4. Run the original comparator

For a check against the fixed benchmark statement, follow the [comparator installation instructions at the same Lean-Eval revision](https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/README.md#5-run-comparator-locally). They specify these tools and source pins:

| Tool | Pinned source commit |
| --- | --- |
| `landrun` | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |
| `lean4export` | `076e8e57707e813375e8f9da8bf989799ace9680` |
| `comparator` | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| `nanoda_bin` | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

Install these outside `verify-dimitrov`, put the binaries on `PATH`, and build the Lean tools with the workspace's exact Lean toolchain as described upstream. Then run from `verify-dimitrov`:

```bash
lake test
```

This runs the original comparator and its independent kernel check. A successful local run checks the submitted theorem against the frozen formal benchmark statement. It is separate from the historical hosted Lean-Eval result linked above, and it does not establish that a formal statement captures every intended informal interpretation.

## Other public records

For each Lean-Eval proof, use its own source manifest and recorded benchmark revision; do not assume all packages use the versions in this example. The [accepted](../accepted/accepted.json) and [submitted](../submitted/submitted.json) indexes link their source records and official results.

The [OpenAI Math records](../data/proofs/) publish statements, proof source, verification reports, and research processes. Their reported local Lean and original-comparator checks are distinct from OpenAI-hosted evaluation, whose results have not been confirmed. Use each record's own statement and environment rather than applying this Dimitrov workspace to those files.
