<div align="center">

<img src="assets/mark.png" alt="" width="64" height="64">

<h1>TheoremOS</h1>

<p><strong>From mathematical problems to independently checked Lean proofs.</strong></p>
<p>A research workbench for mathematicians, Lean users, and math-agent researchers.</p>

<p>
  <a href="https://theoremos.top/en/">Website</a> ·
  <a href="https://theoremos.top/en/#start"><strong>Request research access</strong></a> ·
  <a href="#research-collaboration">Research collaboration</a> ·
  <a href="https://theoremos.top/en/archive.html">Proof archive</a> ·
  <a href="README.zh-CN.md">简体中文</a>
</p>

</div>

TheoremOS is a browser-based workbench for mathematical research with AI agents, Lean 4, and Mathlib. Enter a problem in natural language or TeX, or start from an existing Lean statement. Choose your model and research budgets, inspect the proof attempts, and download the source and verification report.

A run keeps the statement, candidate proofs, Lean diagnostics, and acceptance record together. Statement meaning review and proof acceptance are shown separately, so you can check the formalization against the original problem.

**26 public proof records:** [10 official Lean-Eval passes](#lean-eval-10-official-passes) and [16 locally verified OpenAI Math records](#openai-math-16-locally-verified-problem-records). The collection includes work by TheoremOS and its predecessors, DeepScientist and DeepScientist Math, with attribution preserved for each record.

<a href="https://theoremos.top/en/#start">
  <picture>
    <source media="(max-width: 640px)" srcset="assets/workbench-mobile.png">
    <img src="assets/workbench-desktop.png" alt="TheoremOS natural-language entry screen, showing problem input, model settings, and formalization and proof budgets; Chinese interface" width="1440">
  </picture>
</a>

<p align="center"><sub>Natural-language entry · Chinese interface · <a href="assets/workbench-full-desktop.png">Full screenshot</a></sub></p>

## Selected examples

Open the statement, proof, and acceptance evidence to inspect what each case establishes. The local records also include the recorded research process.

| Case | What was checked | Source and evidence |
| --- | --- | --- |
| [Hopf–Rinow](accepted/hopf_rinow/) | Equivalence of geodesic and metric completeness under the archived manifold hypotheses. | [Proof](accepted/hopf_rinow/Submission.lean) · [Official pass](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| Planar Anderson spectrum | For `h > 0` and independent uniform potentials on `[-h, h]`, the almost-sure spectrum is `[-4-h, 4+h]`. | [Statement](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [Proof](data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [Local pass](data/proofs/openai_planar_anderson_spectrum/verification.json) · [Process](data/proofs/openai_planar_anderson_spectrum/process.json) |
| Three-state tree reconstruction | Under the archived supercritical hypotheses, reconstruction advantages on regular and Poisson trees converge to positive limits. | [Statement](data/proofs/openai_three_state_supercritical/Challenge.lean) · [Proof](data/proofs/openai_three_state_supercritical/Submission.lean) · [Local pass](data/proofs/openai_three_state_supercritical/verification.json) · [Process](data/proofs/openai_three_state_supercritical/process.json) |
| Snaky winning strategy | A legal strategy completes a Snaky within 35 Maker moves against legal replies. | [Statement](data/proofs/openai_snaky_conditional/Challenge.lean) · [Proof](data/proofs/openai_snaky_conditional/Submission.lean) · [Local pass](data/proofs/openai_snaky_conditional/verification.json) · [Process](data/proofs/openai_snaky_conditional/process.json) |

[See all 26 records and their verification evidence](#proofs-and-verification).

## Research collaboration

We welcome joint studies with a concrete mathematical or methodological question:

- Bring a problem with precise hypotheses. We can work together on its Lean statement and proof routes.
- Bring an unfinished Lean proof. We can examine the missing lemmas and identify reusable results.
- Bring a search, context selection, or collaboration strategy. We can design a comparison with the statement, model, environment, and budget held fixed.

Email [liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn) with a problem source or Lean statement, what you have tried, and the question you want to investigate. Public questions and product feedback can go in [Issues](https://github.com/LikC1606/theorem-os-site/issues/new).

## Start a study

The workbench is an **allowlist beta**. The platform is free during beta; your model provider bills API calls. Browser use requires no local Lean or Docker installation.

1. [Request access](https://github.com/LikC1606/theorem-os-site/issues/new?template=early-access.yml) with your research use and a problem you want to work on. You can also apply privately by emailing [liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn).
2. Sign in at [app.theoremos.top](https://app.theoremos.top/). Connect OpenAI or a service compatible with the Responses API using your own API key, and set the formalization and proof budgets.
3. Submit natural language, TeX, or an existing Lean statement. Review the formalization, follow the proof attempts, and download the Lean source, verification report, and local verification kit.

We reply to access requests in the same issue and arrange sign-in addresses privately. GitHub issues are public; keep API keys and personal contact details out of them.

Lean acceptance applies to the fixed formal statement. Review that statement against your original problem. To explore first without a key, [browse the archive](https://theoremos.top/en/archive.html) or [watch the preset verification replay](https://theoremos.top/en/#demo).

## Proofs and verification

The full repository collection is listed below. For each local OpenAI Math record:

1. Read the frozen statement in `Challenge.lean` alongside the accepted `Submission.lean`, including its hypotheses.
2. Check the target names, `proofSha256`, `kernelStatus`, and `comparatorExitCode` in `verification.json`.
3. Match its `runId` to `process.json` to inspect the recorded tasks, proof attempts, and events.

### Lean-Eval: 10 official passes

<details>
<summary>View all 10 proof packages and official results</summary>

| Proof package | Area | Official result |
| --- | --- | --- |
| [Unit conjecture: a nontrivial group-ring unit](accepted/annals_unit_conjecture/) | Algebra | [#1246 · pass](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| [Rademacher type and Enflo type coincide](accepted/annals_rademacher_enflo_type/) | Functional analysis | [#2115 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| [Equiangular lines with a fixed angle](accepted/annals_equiangular_lines_fixed_angle/) | Discrete geometry | [#2135 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |
| [Fractional expectation thresholds](accepted/annals_fractional_expectation_thresholds/) | Probabilistic combinatorics | [#2141 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2141#issuecomment-6197783762) |
| [Dimitrov's lower bound for algebraic integers](accepted/dimitrov/) | Algebraic number theory | [#2143 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [Hopf–Rinow theorem](accepted/hopf_rinow/) | Riemannian geometry | [#2143 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [Improved bounds for the sunflower lemma](submitted/annals_improved_bounds_sunflower_lemma/) | Combinatorics | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [Lorentzian polynomials](submitted/annals_lorentzian_polynomials/) | Algebraic combinatorics | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [The optimal paper Möbius band](submitted/annals_optimal_moebius/) | Geometry | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [Algebraic integers: an upper bound for λ_SSS](submitted/annals_algebraic_integers/) | Algebraic number theory | [#2144 · pass](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |

These packages include results from DeepScientist / DeepScientist Math and subsequent work, including continuation runs and environment migrations. Original model attribution, source revisions, and SHA-256 checksums are preserved in [accepted.json](accepted/accepted.json) and [submitted.json](submitted/submitted.json). These archived outcomes do not measure the current release's success rate on fresh runs.

The last four packages passed together in [submission #2144](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) and retain their original `submitted/` paths. Official acceptance is recorded in the linked Lean-Eval responses; local `verification.json` files describe checks for a particular source and environment.

</details>

### OpenAI Math: 16 locally verified problem records

<details>
<summary>View all 16 problems, proof source, and local verification records</summary>

Each problem has a native TheoremOS `evaluated_passed` record, a Lean kernel check, and a successful local run of the original comparator. These are local verification records; OpenAI-hosted acceptance is unconfirmed.

| Problem record | Area | Statement and proof | Verification and process |
| --- | --- | --- | --- |
| Supercritical three-state reconstruction on regular and Poisson trees | Probability | [Statement](data/proofs/openai_three_state_supercritical/Challenge.lean) · [Proof](data/proofs/openai_three_state_supercritical/Submission.lean) | [Local pass](data/proofs/openai_three_state_supercritical/verification.json) · [Process](data/proofs/openai_three_state_supercritical/process.json) |
| Face correspondence under triangle expansion | Combinatorial optimization | [Statement](data/proofs/openai_triangle_face/Challenge.lean) · [Proof](data/proofs/openai_triangle_face/Submission.lean) | [Local pass](data/proofs/openai_triangle_face/verification.json) · [Process](data/proofs/openai_triangle_face/process.json) |
| Endpoint non-integrability for the Koebe map and its inverse | Complex analysis | [Statement](data/proofs/openai_brennan_sharp/Challenge.lean) · [Proof](data/proofs/openai_brennan_sharp/Submission.lean) | [Local pass](data/proofs/openai_brennan_sharp/verification.json) · [Process](data/proofs/openai_brennan_sharp/process.json) |
| Support results on numerical ranges and finite-dimensional compressions | Functional analysis | [Statement](data/proofs/openai_hilbert_crouzeix/Challenge.lean) · [Proof](data/proofs/openai_hilbert_crouzeix/Submission.lean) | [Local pass](data/proofs/openai_hilbert_crouzeix/verification.json) · [Process](data/proofs/openai_hilbert_crouzeix/process.json) |
| Almost-sure spectrum of the planar Anderson operator | Random operators | [Statement](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [Proof](data/proofs/openai_planar_anderson_spectrum/Submission.lean) | [Local pass](data/proofs/openai_planar_anderson_spectrum/verification.json) · [Process](data/proofs/openai_planar_anderson_spectrum/process.json) |
| Finiteness of the Ising-perceptron variational value | Probability and statistical physics | [Statement](data/proofs/openai_ising_finiteness/Challenge.lean) · [Proof](data/proofs/openai_ising_finiteness/Submission.lean) | [Local pass](data/proofs/openai_ising_finiteness/verification.json) · [Process](data/proofs/openai_ising_finiteness/process.json) |
| Totient companion: the no-seed zero case | Number theory | [Statement](data/proofs/openai_totient_companion_zero/Challenge.lean) · [Proof](data/proofs/openai_totient_companion_zero/Submission.lean) | [Local pass](data/proofs/openai_totient_companion_zero/verification.json) · [Process](data/proofs/openai_totient_companion_zero/process.json) |
| Compactness of normalized Cartier chart retractions | Algebraic geometry and topology | [Statement](data/proofs/openai_cartier_chart_compactness_support/Challenge.lean) · [Proof](data/proofs/openai_cartier_chart_compactness_support/Submission.lean) | [Local pass](data/proofs/openai_cartier_chart_compactness_support/verification.json) · [Process](data/proofs/openai_cartier_chart_compactness_support/process.json) |
| A colored-graph criterion for finite congruence lattices | Universal algebra and lattice theory | [Statement](data/proofs/openai_finite_congruence_graph/Challenge.lean) · [Proof](data/proofs/openai_finite_congruence_graph/Submission.lean) | [Local pass](data/proofs/openai_finite_congruence_graph/verification.json) · [Process](data/proofs/openai_finite_congruence_graph/process.json) |
| Existence of the honeycomb free-energy limit | Probability and statistical physics | [Statement](data/proofs/openai_honeycomb_free_energy/Challenge.lean) · [Proof](data/proofs/openai_honeycomb_free_energy/Submission.lean) | [Local pass](data/proofs/openai_honeycomb_free_energy/verification.json) · [Process](data/proofs/openai_honeycomb_free_energy/process.json) |
| A seven-coloring of the Euclidean plane | Discrete geometry | [Statement](data/proofs/openai_plane_coloring/Challenge.lean) · [Proof](data/proofs/openai_plane_coloring/Submission.lean) | [Local pass](data/proofs/openai_plane_coloring/verification.json) · [Process](data/proofs/openai_plane_coloring/process.json) |
| A legal 35-move winning strategy for Snaky | Combinatorial games | [Statement](data/proofs/openai_snaky_conditional/Challenge.lean) · [Proof](data/proofs/openai_snaky_conditional/Submission.lean) | [Local pass](data/proofs/openai_snaky_conditional/verification.json) · [Process](data/proofs/openai_snaky_conditional/process.json) |
| Snaky certificate verification | Combinatorial games | [Statement](data/proofs/openai_snaky_certificate/Challenge.lean) · [Proof](data/proofs/openai_snaky_certificate/Submission.lean) | [Local pass](data/proofs/openai_snaky_certificate/verification.json) · [Process](data/proofs/openai_snaky_certificate/process.json) |
| Hadamard cube-fiber cancellation | Linear algebra | [Statement](data/proofs/openai_hadamard_cube_fiber/Challenge.lean) · [Proof](data/proofs/openai_hadamard_cube_fiber/Submission.lean) | [Local pass](data/proofs/openai_hadamard_cube_fiber/verification.json) · [Process](data/proofs/openai_hadamard_cube_fiber/process.json) |
| A three-dimensional complete normal local complex algebra | Commutative algebra | [Statement](data/proofs/openai_surface_cone_candidate_support/Challenge.lean) · [Proof](data/proofs/openai_surface_cone_candidate_support/Submission.lean) | [Local pass](data/proofs/openai_surface_cone_candidate_support/verification.json) · [Process](data/proofs/openai_surface_cone_candidate_support/process.json) |
| A finite counterexample to Truffet's procedure | Tropical optimization | [Statement](data/proofs/openai_truffet_counterexample/Challenge.lean) · [Proof](data/proofs/openai_truffet_counterexample/Submission.lean) | [Local pass](data/proofs/openai_truffet_counterexample/verification.json) · [Process](data/proofs/openai_truffet_counterexample/process.json) |

The count follows archived problem records, each of which may contain multiple fixed theorem declarations. The Snaky strategy and certificate are separate records; the Totient result covers the no-seed zero case. Each record preserves its exact statements, source hash, and attribution, including external mathematical assistance, saved-candidate handoffs, or continuation runs where recorded.

</details>

For the recorded research processes, open the [interactive proof archive](https://theoremos.top/en/archive.html). Historical research snapshots carry separate status labels.

## Repository contents

TheoremOS is closed-source software. This repository publishes the website, proof source, and research records; the runtime source is private.

<details>
<summary>Repository layout and licensing</summary>

| Path | Contents |
| --- | --- |
| [accepted/](accepted/) | Six proof packages with official Lean-Eval passes and provenance records |
| [submitted/](submitted/) | Four further officially accepted proof packages from submission #2144 |
| [data/proofs/](data/proofs/) | Sixteen locally verified OpenAI Math problem records, with statements, proof source, verification reports, and process records |
| [in-progress/](in-progress/) | Selected historical Lean research snapshots; unfinished drafts may contain `sorry` |
| [data/catalog.json](data/catalog.json) | The interactive archive's catalog, including status and evidence links |
| `index.html`, `archive.html`, `feedback.html`, `en/`, `assets/` | Published website, English pages, and interface screenshots |

TheoremOS reserves all rights to its runtime. Third-party fonts and icons retain their accompanying licenses in [assets/fonts/](assets/fonts/), [assets/licenses/](assets/licenses/), and [lucide-LICENSE.txt](lucide-LICENSE.txt).

</details>
