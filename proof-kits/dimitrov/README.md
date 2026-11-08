# Dimitrov Theorem Standalone Proof Kit

[简体中文](./README.zh-CN.md) | [Back to Repository README](https://github.com/LikC1606/TheoremOS/blob/main/README.md) | [Verification Guide](https://github.com/LikC1606/TheoremOS/blob/main/docs/VERIFY.md)

This proof kit provides a self-contained local workspace for mathematicians and formal verification researchers to re-verify the formal proof of `Submission.dimitrov` on Linux using the pinned Lean 4 kernel and upstream comparators, without a TheoremOS account, API key, or model calls.

## Mathematical statement and pinned environment

- **Theorem (`Submission.dimitrov`)**: Under the problem's hypotheses for a non-zero algebraic integer that is not a root of unity, its house (the maximum modulus of its conjugates) satisfies an explicit lower bound in terms of the number of arguments among its complex embeddings. See [`Challenge.lean`](./Challenge.lean) for the formal statement and [`Submission.lean`](./Submission.lean) (with [`Submission/Helpers.lean`](./Submission/Helpers.lean)) for the proof.
- **Unmodified upstream and archive files**: The problem statement (`Challenge.lean`), solution bridge and test harness (`Solution.lean`, `WorkspaceTest.lean`), comparator config (`config.json`, `holes.json`), archived proof files (`Submission.lean`, `Submission/Helpers.lean`), and toolchain/manifest files (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) are copied byte-for-byte from upstream or the public archive. `Check.lean`, `verify.py`, and `install-tools.sh` are verification helpers added for this kit.
- **Pinned versions and provenance**:
  - Lean toolchain: `leanprover/lean4:v4.35.0-rc3`
  - Mathlib commit: `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`
  - Lean-Eval commit: `38361be884302c7edce1908c4aef8296eb2cb27e`
  - Historical upstream acceptance: [leanprover/lean-eval-submissions#2143 (comment)](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969)
  - Provenance for copied upstream/archive files is recorded in [`sources.json`](./sources.json); SHA256 digests for all files in the kit (including added scripts and docs) are in [`SHA256SUMS`](./SHA256SUMS).

## Obtaining the kit and checking integrity

You can either `cd proof-kits/dimitrov` inside a clone of the public repository, or download the standalone release archive:

- ZIP archive: [theoremos-dimitrov-proof-kit-20261108.zip](https://github.com/LikC1606/TheoremOS/releases/download/v0.1.0-preview.1/theoremos-dimitrov-proof-kit-20261108.zip)
- SHA256 file: [theoremos-dimitrov-proof-kit-20261108.zip.sha256](https://github.com/LikC1606/TheoremOS/releases/download/v0.1.0-preview.1/theoremos-dimitrov-proof-kit-20261108.zip.sha256)

After downloading both files into the same directory, verify the checksum, extract the archive, and enter the kit directory:

```bash
sha256sum -c theoremos-dimitrov-proof-kit-20261108.zip.sha256
unzip theoremos-dimitrov-proof-kit-20261108.zip
cd theoremos-dimitrov-proof-kit
```

## System requirements

- **Base tools**: `git`, `python3`, `elan` (see the [official Lean install guide](https://lean-lang.org/install/)), and network access. The kit does not bundle multi-gigabyte precompiled Mathlib caches, so the first run downloads dependencies over the network.
- **Full comparator tools**: Running the default full check (upstream comparator plus `nanoda`) requires **Linux** (for `landrun` sandboxing), **Go**, **Rust / Cargo**, and a **C compiler**. `install-tools.sh` builds the external verification binaries (`lean4export`, `comparator`, `nanoda_bin`, `landrun`) in an external directory; the two Lean tools use the kit's exact Lean version; it does not install the TheoremOS runtime.

## Step-by-step verification commands

Run these commands from the proof kit root. Any non-zero exit code indicates a check failure.

### Step 1: Check file hashes

Validate all bundled files against `SHA256SUMS` without invoking Lean:

```bash
python3 verify.py --check-files
```

### Step 2: Prepare dependencies and run the Lean-only check

The first run requires `--prepare`, which fetches dependencies and the Mathlib cache directly from the archived `lake-manifest.json` (do not run `lake update`, which would overwrite the manifest). This builds `Submission` and `Solution` and compiles `Check.lean` so `verify.py` can check the axioms of `Submission.dimitrov`. You can stop here if you only want a pure Lean kernel and axiom check; note that `--lean-only` does not run the upstream comparator or `nanoda`:

```bash
python3 verify.py --prepare --lean-only
```

### Step 3: Build external comparator tools and run full verification

The three commands below build the comparator binaries outside the kit directory, load the generated `COMPARATOR_*` environment variables, and run the default full verification (reusing Step 2 builds and running `lake test` with the comparator and `nanoda`):

```bash
bash install-tools.sh "$HOME/.cache/theoremos-proof-tools/dimitrov"
source "$HOME/.cache/theoremos-proof-tools/dimitrov/env.sh"
python3 verify.py
```

If the external comparator tools are missing or not sourced, running `python3 verify.py` builds the Lean targets and then exits non-zero when invoking the comparator rather than downgrading to `--lean-only`.

## Verification rules and reports

- **Axioms and `sorry` handling**: Only `propext`, `Quot.sound`, and `Classical.choice` are permitted; `sorryAx` and custom axioms are rejected. The upstream problem file `Challenge.lean` contains placeholder `sorry` declarations by design; `Check.lean` checks the explicit target type and prints `#print axioms Submission.dimitrov` for `verify.py` to validate, while `lake test` compares against the frozen statement and enforces `nanoda`.
- **Logs and reports**: Every run writes step logs and `report.json` to `verification-output/`. The kit also includes the historical archive record [`verification.json`](./verification.json) and the validation report for this release [`validation/report.json`](./validation/report.json).
- **Validation summary for this kit**: On 2026-11-08, `Submission` / `Solution` compilation, target-type and axiom checks, and the original `lake test` all passed. The original comparator, Lean default kernel, and independent `nanoda` kernel accepted the proof. Its axioms are `Classical.choice`, `Quot.sound`, and `propext`.

## Licensing and attribution

Upstream Lean-Eval workspace files remain under [`LICENSE.lean-eval`](./LICENSE.lean-eval) (Apache-2.0; see [`UPSTREAM-README.md`](./UPSTREAM-README.md)), while TheoremOS verification scripts and packaging are under [`LICENSE.TheoremOS`](./LICENSE.TheoremOS) and original archive attributions. Distributing this kit does not re-license the bundle or the TheoremOS runtime under Apache-2.0.
