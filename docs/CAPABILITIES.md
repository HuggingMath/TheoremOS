# TheoremOS Capabilities and Scope of Collaboration

[简体中文](./CAPABILITIES.zh-CN.md) | [Back to README](../README.md) | [Early Access](./ACCESS.md) | [Getting Started](./GETTING-STARTED.md) | [Case Study](./CASE-STUDY.md) | [Proof Archive & Observations](./EVALUATION.md) | [Verification Guide](./VERIFY.md)

TheoremOS helps mathematicians and formalization researchers check formal statements, propose helper lemmas, guide multi-agent proof exploration, and verify final proofs in Lean 4. The system handles formalization steps, branch trial-and-error, and kernel checking so researchers can focus on mathematical constructions, lemma decomposition, and proof plans.

The tables below list what is available today in the browser workspace (research preview), what is available through CLI research collaboration, and what remains planned.

## Browser workspace capabilities (research preview)

The web workspace (`https://app.theoremos.top`) is built for self-contained mathematical propositions with explicit assumptions and conclusions, as well as single-file Lean tasks expressible in the platform's pinned Lean standard library or Mathlib environment.

| Area | Entry point | Behavior and current boundaries |
| :--- | :--- | :--- |
| Access and billing | Global web workspace<br>[Access guide](./ACCESS.md) | Available via email-allowlisted research preview. The platform is free; users bring their own Responses API key and pay model providers directly. Request access via [GitHub Issue](https://github.com/LikC1606/TheoremOS/issues/new?template=early-access.yml) or email `liuzhenhao@westlake.edu.cn` (never post API keys in public Issues). |
| Natural language, TeX, and Lean input | Home page / Advanced Lean entry | The home page accepts natural language or TeX problem statements. Advanced Lean accepts pasting or importing a single `.lean` file (including incomplete proofs with `sorry`). Tasks run in a fixed Lean standard library or Mathlib environment (versions and storage limits are shown in the UI); the web app does not upload arbitrary multi-file Lake projects. |
| Formal statement review | Home page / [Standalone formalize page](https://app.theoremos.top/formalize.html) | Generated Lean statements undergo compilation checks and back-translation comparison to help catch missing hypotheses or quantifier drift, though human review is still needed to confirm equivalence with the informal problem. The home page starts proving automatically after review. To inspect the statement first, use `formalize.html`, carry it into a research draft or Advanced Lean entry, and start proving manually. `formalize.html` uses its own default model and budget rather than home page settings or one-time keys. |
| Provider and model setup | Model settings panel | Select from platform-deployed providers and enter a model name and API key. Custom Base URLs are not supported in the web UI. "Check Key & Model" only checks model-list connectivity, not theorem-proving capability. |
| Budgets and stopping | Home settings / Advanced Lean settings | Set time and token limits for formalization and proving on the home page; Advanced Lean also sets research rounds and agent counts. Runs stop based on provider-reported usage. Because in-flight requests finish before reporting, these limits are not hard billing caps. |
| Multi-agent collaboration and guidance | Advanced Lean entry | Configure 1–4 agents in task-collaborative or independent-parallel mode. Roles cover Lead, Researcher, Engineer, and Reviewer as needed rather than a fixed four-agent team or fixed five-stage pipeline. You can enter research guidance and edit the proof plan directly. "Review plan before starting" requires collaborative mode with at least 2 agents; home page auto-proving defaults to 1 agent. |
| Strategy presets and scheduling | Advanced Lean strategy panel | Includes presets for plan-driven execution, critical-path priority, and proof-frontier continuation, plus full/compact context toggles, saved profiles, and text guidance for M1/M3/M4/M5 decision points. These guide prompting and scheduling without uploading executable plugins or changing final Lean verification rules. |
| Account verified lemma catalog | Advanced web catalog / CLI | Search your account's verified lemma catalog in the Advanced web UI, inspect types, premises, code, and provenance, and select catalogs for a run to snapshot a fixed runtime version (reused lemmas are still re-checked by Lean in the new proof environment). The CLI adds catalog construction and bulk import tools. |
| Process view, archives, and review kits | Run details / Archive manager | View proof code, verification reports, and research logs in the browser, or export archives and candidate proof review kits. Importing a draft or archive restores inputs and settings without replaying or restoring full execution state (process storage is capacity-limited). Compiling helper lemmas does not mean the main theorem is complete. |

## Research collaboration and CLI capabilities

For work that goes beyond single-file web tasks or requires source-level policy experiments, contact us at `liuzhenhao@westlake.edu.cn`:

| Track | When to use | Scope and boundaries |
| :--- | :--- | :--- |
| Policy replacement and ablations | Algorithmic research collaboration | Source-level replacement of M1–M5 decision policies via our CLI research collaboration interface, controlled budget ablations, and bulk lemma catalog pipelines. |
| Multi-file projects and custom toolchains | Joint mathematical research | For projects requiring custom packages, private dependencies, multi-file Lake repositories, or custom Mathlib/Lean toolchains, please contact us to discuss adaptation and collaboration scope. |
| Repository and distribution scope | Public repo vs. runtime | This repository publishes web documentation, public proof archives, and standalone verification materials. The TheoremOS runtime and CLI have no public source release or installer; web preview access does not grant a source code license. |

## Architecture status: implemented vs. planned

| Module | Status | What it does |
| :--- | :--- | :--- |
| S1 Structured archiving | Implemented | Stores formal statements, exploration records, candidate proof files, and environment metadata (within storage limits) for workspace inspection and archive review. |
| S3 Formal verification | Implemented | Runs a fixed independent Lean 4 check on final proofs, plus the benchmark's pinned comparator when verifying benchmarks that provide one. Unverified prose or open `sorry` placeholders never count as completed proofs. |
| S2 Continuous learning | Planned | Current lemma catalog search and archive reuse are retrieval and engineering reuse mechanisms; they do not perform automated weight training or continuous self-learning. |

## Choosing a workflow

1. **Working on a theorem or lemma**: Request web preview access. Use the [Standalone formalize page](https://app.theoremos.top/formalize.html) to check and approve the Lean statement, carry it into a research draft or Advanced Lean entry, choose the number of agents you need, and edit the research plan to guide the proof.
2. **Checking published proofs locally**: Follow the [Verification Guide](./VERIFY.md) or download the [Dimitrov Standalone Proof Kit](../proof-kits/dimitrov/README.md) to run the Lean kernel and comparator on your own Linux machine without an account or API key.
3. **Custom repositories or policy experiments**: Email `liuzhenhao@westlake.edu.cn` to discuss CLI collaboration and project adaptation.
