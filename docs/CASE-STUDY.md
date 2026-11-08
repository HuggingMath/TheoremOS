# Case Study: Almost-Sure Spectrum of the Planar Anderson Operator

[简体中文](CASE-STUDY.zh-CN.md) · [Back to README](../README.md)

In mathematical research, formalizing arguments that combine operator spectral theory, probability spaces, and lattice limits requires resolving numerous low-level technical lemmas. TheoremOS is an AI mathematical research system built to collaborate with mathematicians: it accepts natural language, $`\TeX`$, and Lean 4 inputs, decomposes theorems into verifiable subgoals, explores proof strategies, and checks complete submitted proofs with an independent Lean 4 kernel.

This case study examines a complete formalization from our public archive: characterizing the almost-sure spectrum of the two-dimensional discrete Anderson Hamiltonian. Every definition, lemma, and kernel check discussed below can be inspected directly in the [interactive proof archive](https://theoremos.top/en/archive.html#proof=openai_planar_anderson_spectrum) and the [process archive](https://theoremos.top/en/archive.html#proof=openai_planar_anderson_spectrum&tab=process).

## Problem Formulation and Formal Target

Consider the complex Hilbert space $`\ell^2(\mathbb{Z}^2)`$ on the two-dimensional integer lattice. The planar tight-binding Anderson operator $`H = \Delta + V`$ acts on $`\psi \in \ell^2(\mathbb{Z}^2)`$ as the sum of four nearest-neighbor shifts and multiplication by a real random potential:

$$(H\psi)(x) = \psi(x+e_1) + \psi(x-e_1) + \psi(x+e_2) + \psi(x-e_2) + V(x)\psi(x)$$

where $`e_1=(1,0)`$ and $`e_2=(0,1)`$. The potential values $`\lbrace V(x)\rbrace _{x \in \mathbb{Z}^2}`$ are independent and identically distributed uniform random variables on $`[-h, h]`$ for $`h > 0`$. The theorem states that almost surely, the spectrum of $`H`$ is the closed interval $`[-4-h, 4+h]`$.

In the formal problem specification [`Challenge.lean`](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean), the target theorem `OAI.PlanarAnderson.anderson_spectrum_ae` requires more than identifying the interval: one must prove that for almost every sample $`\omega`$, a bounded linear operator $`H(\omega)`$ satisfying the pointwise action formula exists, is self-adjoint (`IsSelfAdjoint`), and has its complex spectrum $`\sigma_{\mathbb{C}}(H(\omega))`$ equal to the image of $`[-4-h, 4+h]`$ in $`\mathbb{C}`$.

## Proof Architecture and Lean 4 Implementation

On paper, the upper spectral inclusion follows from operator norm bounds, while the lower inclusion uses Weyl's approximate eigenvalue criterion (an approximate eigenvector argument) supported on large finite boxes where the random potential is nearly constant. Translating this into a `sorry`-free Lean 4 proof requires explicit measure-theoretic quantification and rigorous discrete boundary estimates.

In [`Submission.lean`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean) (1,454 lines), the system establishes the theorem across five main stages:

| Mathematical Stage | Key Lean Declarations (Source Links) | Formalized Content |
| :--- | :--- | :--- |
| 1. Operator Construction & Upper Bound | [`anderson_operator_exists_selfAdjoint`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L224)<br>`anderson_spectrum_subset` | Constructs $`H`$ as `adjacencyCLM + mulCLM hv`, proves self-adjointness and $`\Vert H\Vert  \le 4+h`$, and combines real-spectrum properties with the norm bound to establish $`\sigma(H) \subseteq [-4-h, 4+h]`$. |
| 2. Occurrence of Near-Constant Blocks | [`constant_block_occurrence`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L485) | Uses independence across disjoint finite boxes and positive uniform measure to show that for a fixed target $`c \in [-h,h]`$, error $`\varepsilon > 0`$, and box size $`N`$, a translated box with $`\vert V(x)-c\vert  < \varepsilon`$ occurs almost surely. |
| 3. Countable Intersection & Quantifier Exchange | [`ae_blocks_simultaneous`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L921) | Bridges pointwise almost-sure statements via rational approximation and countable intersections, yielding a single probability-one event on which near-constant blocks exist simultaneously for all required constants and scales. |
| 4. Cut-off Plane Waves & Lower Bound | [`finite_box_approx_eigenvector`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1206)<br>[`spectrum_lower_of_blocks_pos`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1252) | Constructs normalized truncated plane waves $`u`$ on large boxes, bounds boundary leakage and potential deviation so $`\Vert (H-\lambda I)u\Vert `$ is arbitrarily small, and applies [`approx_eigenvalue_mem_spectrum`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L281) to conclude $`\lambda \in \sigma(H)`$. |
| 5. Main Theorem Assembly | [`anderson_spectrum_ae`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1446) | Preserves the exact type signature from the challenge file and closes the goal via the helper theorem `exact anderson_spectrum_ae_sorry_free hh`. |

### Core Formalization Challenge: Exchanging Quantifiers with "Almost Everywhere"

A central technical hurdle appears in Stage 3 ([`ae_blocks_simultaneous`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L921)). In informal expositions, one readily moves from "for every $`c \in [-h,h]`$, almost surely a box with potential near $`c`$ exists" to the full spectral interval. Formally, however, $`\forall c \in [-h,h],\, \mathbb{P}(\Omega_c)=1`$ does not directly imply $`\mathbb{P}(\bigcap_{c \in [-h,h]} \Omega_c)=1`$, because an uncountable intersection of full-measure sets need not have full measure.

`Submission.lean` resolves this by taking a countable intersection over triples $`(c', \varepsilon', N) \in \mathbb{Q} \times \mathbb{Q} \times \mathbb{N}`$ with $`c' \in [-h,h]`$ and $`\varepsilon' > 0`$. This yields a single measurable event $`\Omega_0`$ of probability one. Fixing any sample $`\omega \in \Omega_0`$, any real potential value $`c \in [-h,h]`$, and any tolerance $`\varepsilon > 0`$, the proof selects a nearby rational $`c' \in [-h,h]`$ and rational tolerance $`\varepsilon' > 0`$, transferring the block property from $`c'`$ to $`c`$ via the triangle inequality. Similarly, Stage 4 replaces informal asymptotic arguments with explicit $`\ell^2`$ norm decompositions separating interior cancellations from boundary terms, showing that the boundary error vanishes as the box size grows.

## Process Archive and Collaborative Perspective

The [process archive](https://theoremos.top/en/archive.html#proof=openai_planar_anderson_spectrum&tab=process) and [`process.json`](../data/proofs/openai_planar_anderson_spectrum/process.json) record the full task decomposition tree. Alongside the completed finite-box and approximate-eigenvector route, the public record also retains unfinished alternative branches—such as `constant_potential_spectrum`, `constant-box-bridge`, and `weyl-fallback` (marked `blocked` or `pending`)—which can be compared directly against the final proof.

The archived record includes historical continuations (with events recorded starting 2026-10-28). No external mathematical edits were found in the accepted run. When mathematicians use TheoremOS in their own research, this decomposition workflow serves as the point of collaboration: researchers can verify formal definitions before proof search begins, inspect competing branches to decide which analytical route merits further budget, or supply intermediate lemmas when a subgoal stalls.

## Independent Kernel Verification

As recorded in [`verification.json`](../data/proofs/openai_planar_anderson_spectrum/verification.json), the submission passed both the independent Lean 4 kernel check and the challenge comparator run by our verification pipeline:

* **Verification Status**: `status = evaluated_passed`, `kernelStatus = kernel_verified`, `comparatorExitCode = 0`, `reviewStatus = accepted`.
* **Comparator Output**: Includes `Lean default kernel accepts the solution` and `Your solution is okay!`.
* **Axiom Audit**: According to `runs[0].review.summary` in `process.json`, the target theorem and its supporting lemmas depend solely on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom axioms.

> **Note on Evaluation Status**: This proof has passed the Lean kernel and challenge comparator checks run by our project; **official OpenAI evaluation results are not yet confirmed**.

<details>
<summary>Artifact Links and SHA-256 Checksum</summary>

* Problem template (contains placeholder `sorry` in the statement file): [`Challenge.lean`](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean)
* Complete formal proof: [`Submission.lean`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean) (SHA-256: `2fd7e2d1c71eff673ce58cd82f694526f9d6ed0a4ace42f800b159b26482cfc7`, matching the verification record)
* Kernel verification log: [`verification.json`](../data/proofs/openai_planar_anderson_spectrum/verification.json)
* Process and run log: [`process.json`](../data/proofs/openai_planar_anderson_spectrum/process.json)

</details>

## Further Resources

* **Raw Proof Artifacts**: [Challenge.lean](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [Submission.lean](../data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [verification.json](../data/proofs/openai_planar_anderson_spectrum/verification.json) · [process.json](../data/proofs/openai_planar_anderson_spectrum/process.json)
* **Interactive Viewer**: [Proof Archive](https://theoremos.top/en/archive.html#proof=openai_planar_anderson_spectrum) · [Process View](https://theoremos.top/en/archive.html#proof=openai_planar_anderson_spectrum&tab=process)
* **Getting Started & Local Verification**: Follow the [Getting Started Guide](GETTING-STARTED.md) to run your first session on the cloud workbench, or see [`VERIFY.md`](VERIFY.md) to reproduce kernel checks locally.
* **Research Collaboration**: See [`ACCESS.md`](ACCESS.md) for access details, or contact `liuzhenhao@westlake.edu.cn` for academic collaboration.
