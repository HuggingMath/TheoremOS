# TheoremOS Capabilities and Scope of Collaboration

[简体中文](./CAPABILITIES.zh-CN.md) | [Back to README](../README.md) | [Early Access](./ACCESS.md) | [Getting Started](./GETTING-STARTED.md) | [Case Study](./CASE-STUDY.md) | [Proof Archive & Observations](./EVALUATION.md) | [Verification Guide](./VERIFY.md)

TheoremOS helps mathematicians and formalization researchers check formal statements, propose helper lemmas, guide multi-agent proof exploration, and verify final proofs in Lean 4. The system handles formalization steps, branch trial-and-error, and kernel checking so researchers can focus on mathematical constructions, lemma decomposition, and proof plans.

The tables below list what is available today in the browser workspace (research preview), what is available through CLI research collaboration, and what remains planned.

## Browser workspace capabilities (research preview)

The web workspace (`https://app.theoremos.top`) is built for self-contained mathematical propositions with explicit assumptions and conclusions, as well as single-file Lean tasks expressible in the unified TheoremOS mathematics environment: Lean 4.33.0, Mathlib and 53 TheoremOS library modules. Frozen tasks and historical evidence retain their original environment.

| Area | Entry point | Behavior and current boundaries |
| :--- | :--- | :--- |
| Access and billing | Global web workspace<br>[Access guide](./ACCESS.md) | Available via email-allowlisted research preview. The platform is free; users bring their own Responses API key and pay model providers directly. Request access via [GitHub Issue](https://github.com/LikC1606/TheoremOS/issues/new?template=early-access.yml) or email `liuzhenhao@westlake.edu.cn` (never post API keys in public Issues). |
| Natural language, TeX, and Lean input | Home page / Advanced Lean entry | The home page accepts natural language or TeX problem statements. Advanced Lean accepts pasting or importing a single `.lean` file (including incomplete proofs with `sorry`). New tasks run in the same unified TheoremOS mathematics environment (versions and storage limits are shown in the UI); the web app does not upload arbitrary multi-file Lake projects. |
| Formal statement review | Home page / [Standalone formalize page](https://app.theoremos.top/formalize.html) | Generated Lean statements undergo compilation checks and back-translation comparison to help catch missing hypotheses or quantifier drift, though human review is still needed to confirm equivalence with the informal problem. The home page defaults to Work together: you confirm the meaning, then 2 Agents draft an initial plan and wait for your approval before proving. Selecting Run automatically uses 1 Agent and starts after model review. The optional `formalize.html` page can still confirm a statement and carry it into a research draft. `formalize.html` uses its own default model and budget rather than home page settings or one-time keys. |
| Provider and model setup | Model settings panel | Select from platform-deployed providers and enter a model name and API key. Custom Base URLs are not supported in the web UI. "Check Key & Model" only checks model-list connectivity, not theorem-proving capability. Newly entered keys are temporary by default. Explicitly use the save button in natural-language Settings or the unchecked save checkbox in Lean to save or replace an account key; saved keys can also be deleted. |
| Budgets and stopping | Home settings / Advanced Lean settings | New tasks default to unlimited time and tokens. Set time and token limits for formalization and proving on the home page; Advanced Lean also sets research rounds and agent counts. Plan drafting and revisions consume the proof budget. Pure waiting for human review or approval pauses the proof timer without model calls; approval continues the same run. Runs stop based on provider-reported usage. Because in-flight requests finish before reporting, these limits are not hard billing caps. |
| Multi-agent collaboration and guidance | Home page / Advanced Lean entry | Configure 1–4 agents in task-collaborative or independent-parallel mode. Roles cover Lead, Researcher, Engineer, and Reviewer as needed rather than a fixed four-agent team or fixed five-stage pipeline. You can enter research guidance and edit the proof plan directly. The default home-page Work together mode uses 2 Agents with statement confirmation and initial plan approval; Run automatically uses 1 Agent. In Advanced Lean, "Review plan before starting" requires collaborative mode with at least 2 agents. |
| Strategy presets and scheduling | Advanced Lean strategy panel | Includes presets for plan-driven execution, critical-path priority, and proof-frontier continuation, plus full/compact context toggles, saved profiles, and text guidance for M1/M3/M4/M5 decision points. These guide prompting and scheduling without uploading executable plugins or changing final Lean verification rules. |
| Account verified lemma catalog | Advanced web catalog / CLI | Search your account's verified lemma catalog in the Advanced web UI, inspect types, premises, code, and provenance, and select catalogs for a run to snapshot a fixed runtime version (reused lemmas are still re-checked by Lean in the new proof environment). The CLI adds catalog construction and bulk import tools. |
| Process view, archives, and review kits | Run details / Archive manager | View proof code, verification reports and research logs, or export candidate proof review kits. Run archives include saved events, observations, actions, sources, checks and commands by default, with coverage stating storage limits or records absent from older versions. Importing extracts inputs and settings into a draft without restoring historical execution state. Continue from this version starts a new run from that saved source, retains the frozen original problem and requires new checks and acceptance. Compiling helper lemmas does not mean the main theorem is complete. |

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

1. **Working on a theorem or lemma**: Request web preview access and enter your natural-language or TeX problem on the home page. The default Work together mode asks you to confirm its meaning, review the initial plan from 2 Agents and approve proof execution. Use Advanced Lean for existing Lean source and configurable collaboration, or the optional [Standalone formalize page](https://app.theoremos.top/formalize.html) to review a statement separately.
2. **Checking published proofs locally**: Follow the [Verification Guide](./VERIFY.md) or download the [Dimitrov Standalone Proof Kit](../proof-kits/dimitrov/README.md) to run the Lean kernel and comparator on your own Linux machine without an account or API key.
3. **Custom repositories or policy experiments**: Email `liuzhenhao@westlake.edu.cn` to discuss CLI collaboration and project adaptation.
