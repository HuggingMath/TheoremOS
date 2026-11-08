# Public Proof Archive & Historical Run Observations

[简体中文](./EVALUATION.zh-CN.md) | [Back to README](../README.md) | [Capabilities & Scope](./CAPABILITIES.md) | [Early Access](./ACCESS.md) | [Getting Started](./GETTING-STARTED.md) | [Case Study](./CASE-STUDY.md) | [Verification Guide](./VERIFY.md)

This page summarizes the verified proof archives and historical run records in the public TheoremOS catalog (compiled on `2026-11-08` from the archive snapshot dated `2026-11-07T16:32:08.577Z`). It shows which formal targets have passed Lean verification, how public verification reports link to specific runs, and what statistical limits apply to these historical logs.

This is an inventory of archived research outputs and historical execution logs, not a benchmark conducted on a locked problem set under a uniform budget.

## Public data overview and downloads

You can download the structured datasets and recomputation script directly from this repository:

- Datasets: [snapshot.json](../data/evaluation/snapshot.json), [records.csv](../data/evaluation/records.csv), [runs.csv](../data/evaluation/runs.csv), [selected-run-observations.json](../data/evaluation/selected-run-observations.json)
- Script: [snapshot-evaluation.py](../scripts/snapshot-evaluation.py)

| Metric | Count | Source and notes |
| :--- | :--- | :--- |
| Total public catalog entries | 27 | 26 verified proof archives plus 1 in-progress research snapshot. |
| Official Lean-Eval accepted entries | 10 | 6 from `accepted/accepted.json`; 4 where `submitted/official-results.json` updates historical statuses in `submitted/submitted.json` with manifest hash checks. |
| OpenAI Math formalization archives | 16 | 23 formal targets total; passed our Lean build and original problem comparator checks (not confirmed by official OpenAI evaluation). |
| Unfinished Szemerédi snapshot | 1 | Public catalog status is `in_progress_not_officially_accepted`. |
| Deduplicated `runId`s in OpenAI Math archives | 45 | Extracted from `process.json` across the 16 archives: `evaluated_passed` (19), `limit_reached` (17), `prepared` (4), `runtime_error` (3), `incomplete` (1), `evaluated_failed` (1). Timestamps are present for 38 runs. |

**Notes on counts and run bindings**:

- Because problems were selected for public archiving after successful research, neither `26/27` nor the `19/45` run breakdown across the 16 selected problems can be used to compute a benchmark success rate. Some archives cover helper lemmas (`support`), conditional statements, or multiple formal targets, so a verified archive does not always mean a full solution to the original informal problem.
- Each selected run for the 16 OpenAI Math archives is identified by `verification.json.runId` and linked to preserved raw execution results via its `runId`, solution commit, and proof file SHA256.

## Selected runs for the 16 OpenAI Math archives

The table below lists the 16 selected runs bound via `verification.json.runId`, including problem titles, catalog model labels, durations, rounds, and agent counts:

| Archive / verification | Historical model label | Recorded duration (s) | Turns | Agents |
| --- | --- | --- | --- | --- |
| [Sharp endpoint divergence for the Koebe map](../data/proofs/openai_brennan_sharp/verification.json) | TheoremOS · deepseek-flash | 2,278.193 | 48 | 4 |
| [Normalized Cartier chart retractions](../data/proofs/openai_cartier_chart_compactness_support/verification.json) | TheoremOS · deepseek-flash | 1,144.551 | 6 | 4 |
| [A colored-graph criterion for congruence lattices](../data/proofs/openai_finite_congruence_graph/verification.json) | TheoremOS · deepseek-flash | 1,721.562 | 26 | 4 |
| [Hadamard cube-fiber cancellation](../data/proofs/openai_hadamard_cube_fiber/verification.json) | TheoremOS · deepseek-flash | 966.516 | 4 | 4 |
| [Numerical-range geometry and finite-compression support](../data/proofs/openai_hilbert_crouzeix/verification.json) | TheoremOS · deepseek-flash | 15,498.495 | 55 | 4 |
| [The honeycomb free-energy limit](../data/proofs/openai_honeycomb_free_energy/verification.json) | TheoremOS · deepseek-flash | 3,985.297 | 31 | 4 |
| [Finiteness of the Ising-perceptron variational value](../data/proofs/openai_ising_finiteness/verification.json) | TheoremOS · deepseek-flash | 9,367.002 | 54 | 4 |
| [Almost-sure spectrum of the planar Anderson operator](../data/proofs/openai_planar_anderson_spectrum/verification.json) | TheoremOS · deepseek-flash | 14,032.263 | 107 | 4 |
| [A seven-coloring of the Euclidean plane](../data/proofs/openai_plane_coloring/verification.json) | TheoremOS · deepseek-flash | 8,166.647 | 13 | 4 |
| [The 35-move Snaky certificate](../data/proofs/openai_snaky_certificate/verification.json) | TheoremOS · deepseek-flash | 13,754.834 | 27 | 4 |
| [A 35-move winning strategy for Snaky](../data/proofs/openai_snaky_conditional/verification.json) | TheoremOS · deepseek-flash | 33,443.284 | 7 | 4 |
| [A three-dimensional complete local candidate ring](../data/proofs/openai_surface_cone_candidate_support/verification.json) | TheoremOS · deepseek-flash | 2,073.492 | 10 | 4 |
| [Supercritical reconstruction on regular and Poisson trees](../data/proofs/openai_three_state_supercritical/verification.json) | TheoremOS · deepseek-flash | 13,529.770 | 66 | 4 |
| [Totient companion: zero case](../data/proofs/openai_totient_companion_zero/verification.json) | TheoremOS · deepseek-flash | 3,277.751 | 11 | 4 |
| [Face correspondence under triangle expansion](../data/proofs/openai_triangle_face/verification.json) | TheoremOS · deepseek-flash | 2,843.712 | 18 | 4 |
| [A finite counterexample to Truffet’s procedure](../data/proofs/openai_truffet_counterexample/verification.json) | TheoremOS · deepseek-flash | 839.532 | 1 | 4 |

Duration is `finishedAt - startedAt` for that bound `runId` only; it excludes earlier failed runs, inherited proof drafts, and human analysis time, so it is not total solve time from scratch. Model labels are copied directly from catalog metadata rather than audited per API call. All 16 selected runs used 4 agents.

## Runtime-reported token usage and historical launch budgets

The table below shows `inputTokens`, `outputTokens`, `totalTokens`, and `usageComplete` from each selected run's result record, along with budget settings from the matching launch arguments:

| Archive | Reported input tokens | Reported output tokens | Reported total tokens | Usage complete | Time limit (s) |
| --- | --- | --- | --- | --- | --- |
| [Sharp endpoint divergence for the Koebe map](../data/proofs/openai_brennan_sharp/verification.json) | 73,876,775 | 3,124,376 | 77,001,151 | `false` | 3,597 |
| [Normalized Cartier chart retractions](../data/proofs/openai_cartier_chart_compactness_support/verification.json) | 1,358,267 | 53,475 | 1,411,742 | `false` | 14,400 |
| [A colored-graph criterion for congruence lattices](../data/proofs/openai_finite_congruence_graph/verification.json) | 32,037,290 | 1,202,033 | 33,239,323 | `false` | 14,400 |
| [Hadamard cube-fiber cancellation](../data/proofs/openai_hadamard_cube_fiber/verification.json) | 1,704,708 | 89,908 | 1,794,616 | `false` | Unlimited |
| [Numerical-range geometry and finite-compression support](../data/proofs/openai_hilbert_crouzeix/verification.json) | 81,047,140 | 3,166,088 | 84,213,228 | `false` | Unlimited |
| [The honeycomb free-energy limit](../data/proofs/openai_honeycomb_free_energy/verification.json) | 19,521,397 | 626,066 | 20,147,463 | `false` | 14,400 |
| [Finiteness of the Ising-perceptron variational value](../data/proofs/openai_ising_finiteness/verification.json) | 37,973,642 | 2,165,385 | 40,139,027 | `false` | 14,399 |
| [Almost-sure spectrum of the planar Anderson operator](../data/proofs/openai_planar_anderson_spectrum/verification.json) | 183,936,328 | 7,824,864 | 191,761,192 | `false` | 14,398 |
| [A seven-coloring of the Euclidean plane](../data/proofs/openai_plane_coloring/verification.json) | 12,979,862 | 459,185 | 13,439,047 | `false` | 14,400 |
| [The 35-move Snaky certificate](../data/proofs/openai_snaky_certificate/verification.json) | 104,951,968 | 3,514,812 | 108,466,780 | `false` | Unlimited |
| [A 35-move winning strategy for Snaky](../data/proofs/openai_snaky_conditional/verification.json) | 8,369,984 | 129,494 | 8,499,478 | `false` | Unlimited |
| [A three-dimensional complete local candidate ring](../data/proofs/openai_surface_cone_candidate_support/verification.json) | 9,083,734 | 338,821 | 9,422,555 | `false` | Unlimited |
| [Supercritical reconstruction on regular and Poisson trees](../data/proofs/openai_three_state_supercritical/verification.json) | 132,487,580 | 5,321,780 | 137,809,360 | `false` | Unlimited |
| [Totient companion: zero case](../data/proofs/openai_totient_companion_zero/verification.json) | 4,627,667 | 170,832 | 4,798,499 | `false` | 14,400 |
| [Face correspondence under triangle expansion](../data/proofs/openai_triangle_face/verification.json) | 14,324,003 | 408,272 | 14,732,275 | `false` | Unlimited |
| [A finite counterexample to Truffet’s procedure](../data/proofs/openai_truffet_counterexample/verification.json) | 1,831,984 | 94,339 | 1,926,323 | `true` | Unlimited |

**Three caveats apply to this table**:

- **Incomplete token reporting**: `usageComplete` is `false` in 15 of the 16 selected runs. Only `TruffetCounterexample` has `usageComplete = true`, and that covers only the selected run rather than earlier attempts on the problem. These numbers are runtime-reported tokens only and cannot be summed for total project cost or cross-system efficiency comparisons.
- **`0` means unlimited in launch configs**: Token, round, per-round time, and comparator time caps were `0` across all 16 launches, which means unlimited in the runtime configuration rather than zero usage. Wall-clock caps also varied (some unlimited, others `3597`, `14398`, `14399`, or `14400` seconds), reflecting historical exploration rather than current web workspace defaults.
- **Private raw logs**: Raw result and launch files are private; [selected-run-observations.json](../data/evaluation/selected-run-observations.json) publishes summary fields and SHA256 digests of those private files. Readers can verify proof bindings and recompute the public tables, but cannot audit per-request provider billing from this repository alone.

## Why system-level benchmark metrics are `null`

In [snapshot.json](../data/evaluation/snapshot.json), the following aggregate fields are set to `null` (meaning not established from these records, which is distinct from `0`):

- **Overall benchmark success rate**: `null` (no pre-locked problem set denominator).
- **End-to-end solve time from scratch**: `null` (archives build on earlier iterations and drafts).
- **Full-problem tokens and total cost**: `null` (no uniform protocol, plus `usageComplete=false` in 15/16 selected runs).

## Recomputing and checking the snapshot locally

Run the first command from the repository root to verify that `catalog`, `accepted/accepted.json`, `submitted/official-results.json`, `process.json`, `verification.json`, proof SHA256 digests, and the CSV/JSON tables match; run the second command to regenerate the snapshot files:

```bash
python3 scripts/snapshot-evaluation.py --check
python3 scripts/snapshot-evaluation.py
```
