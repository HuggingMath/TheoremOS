<div align="center">

<img src="assets/mark.png" alt="" width="64" height="64">

<h1>TheoremOS</h1>

<p><strong>面向前沿数学探索的 AI 协同研究系统 · 数学推演与形式化证明平台</strong></p>
<p>检索已有结论 · 并行探索证明路线 · 推导辅助引理 · Lean 引擎严密核查</p>

<p>
  <a href="https://theoremos.top/">🌐 产品官网</a> ·
  <a href="https://theoremos.top/#start"><strong>🚀 申请研究内测</strong></a> ·
  <a href="#与数学家怎样协作">核心机制</a> ·
  <a href="#研究合作">研究合作</a> ·
  <a href="https://theoremos.top/archive.html">📜 证明档案库</a> ·
  <a href="README.md">English</a>
</p>

</div>

**TheoremOS 是一套专为攻克高难度数学问题而设计的 AI 协同研究系统。** 在人机协作流程中，人类数学家负责提出核心问题、注入直觉并把控宏观研究方向；TheoremOS 则根据算力预算自动调度，承担繁琐的文献与结论检索、多路径证明探索以及底层辅助引理的推导，并依托 Lean 引擎对最终证明进行严格的机器核查。

系统大幅降低了形式化工具的工程门槛：研究者只需直接输入自然语言、$\TeX$ 手稿，或已有的 Lean 题目与未完成的证明，即可**在云端完成全流程运行，免去本地配置 Lean 环境与 Docker 部署的繁琐步骤，实现开箱即用**。在推演过程中，系统会完整记录尝试过的每一条探索路线、每一处 Lean 编译报错以及未完成的步骤，并支持保存进度与恢复任务，便于研究者清晰掌握全局推演脉络、及时调整证明策略。

> 🧭 **迈向“Math 2.0”的协同研究范式**：菲尔兹奖得主陶哲轩（Terence Tao）在其[《Math 2.0》博客](https://terrytao.wordpress.com/2026/10/10/math-2-0/)与 [Caltech 公开讲座讲稿](https://teorth.github.io/tao-web/slides/math-2-0-caltech-2026.pdf)（2026 年 10 月）中指出：
>
> *“The more sustainable ‘Math 2.0’ use of AI would be to strengthen all the ways in which human understanding interacts with mathematics.”*（讲稿第 23 页）\
> *（更具可持续性的 AI “Math 2.0” 用法，应当是全方位强化人类理解与数学产生交互的每一种方式。）*
>
> 他同时强调，数学探索应超越单一的解题指标（Beyond problem-solving，第 9、16 页）——探索过程中的收获（包括失败的尝试与阶段性进展）往往比最终解答更具价值；而建设如 Mathlib 般大型高质量的形式化数学库、将零散研究连接为持续更新的知识网络并为证明提供富有动机的清晰解释，正是“Math 2.0”的核心应用方向（第 25 页）。**TheoremOS 的设计理念与这一愿景高度契合：我们不追求替代人类的“黑盒自动解题”，而是致力于通过深度的人机交互、全链路过程留存与形式化成果复用，为数学家提供高效、可靠的研究工具。**

> 🏆 **研究成果与评测表现**：本仓库公开了系统完成的 **26 条高难度前沿数学证明记录**，涵盖代数数论、黎曼几何、泛函分析与统计物理等领域，其中包括 **[10 份通过 Lean-Eval 官方评测的证明](#lean-eval10-份官方通过的证明)**，以及 **[16 条高难度的 OpenAI Math 证明记录](#openai-math16-条证明记录)**。

<a href="https://theoremos.top/#start">
  <picture>
    <source media="(max-width: 640px)" srcset="assets/workbench-mobile.png">
    <img src="assets/workbench-desktop.png" alt="TheoremOS 中文工作台的自然语言入口，展示题目输入、模型设置以及形式化与证明预算" width="1440">
  </picture>
</a>

<p align="center"><sub>云端智能工作台入口 · <a href="assets/workbench-full-desktop.png">点击查看高清完整工作流截图</a></sub></p>

## 与数学家怎样协作

围绕“强化人类理解与数学的交互”，TheoremOS 针对真实的数学研究工作流，构建了高效、透明的人机协同机制：

* **🔄 双向互译与严谨的题意核对**：当输入自然语言或 $\TeX$ 手稿时，系统会先将其转化为形式化的 Lean 定义和定理陈述；在底层编译检查通过后，再将 Lean 陈述**逆向译回直观的数学语言，辅助研究者核对形式化陈述是否符合原意**。系统将“题意核对”与后续的“证明检查”清晰分离，通过人机协同及时发现并减少潜在的语义偏差，提高形式化起点的可靠性。
* **🧠 多角色分工与多路线并行探索**：在寻找证明时，系统既支持单点深度推导，也能按**规划、检索、编写 Lean 证明和审阅**进行精细化分工协作，并行探索多条潜在证明路线。一旦遇到证明缺口，系统会主动检索相关结果、先行尝试推导辅助引理，或及时切换其他备选路线。
* **🔍 全过程透明可控与轨迹留存**：不同于仅输出结果的“黑盒”模式，TheoremOS 将整个研究过程完全透明开放，完整保留每一条分支探索的轨迹。研究者可随时检视此前尝试过的方法、定位 Lean 的具体报错并监控模型算力消耗，从受阻路线中提炼思路，并随时介入、注入专家直觉以调整方向。所有完整题目的最终证明均由独立的 Lean 检查程序严格核验。
* **🏛️ 形式化知识库的沉淀与复用**：呼应“Math 2.0”构建高质量形式化数学库与互联知识网络的愿景，TheoremOS 中所有通过 Lean 检查的定理和辅助引理均可沉淀至知识库，支持按类型、前提和来源进行结构化检索；当将这些成果跨课题复用于其他问题时，系统会在对应的 Lean 环境中重新进行严格核查，让每一次阶段性进展都能成为后续研究的基础。

## 代表案例

从经典几何定理到前沿物理数学模型，TheoremOS 已在多个核心数学分支的高难度问题中展现出可靠的形式化推演能力：

| 证明案例 | 核心数学结论 | 源码、核查与完整推演记录 |
| --- | --- | --- |
| **[Hopf–Rinow 定理](accepted/hopf_rinow/)** | 在题目给定的流形条件下，严格证明测地完备与度量完备等价。 | [Lean 证明](accepted/hopf_rinow/Submission.lean) · [🏅 官方评测通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| **平面 Anderson 算子谱** | 当 `h > 0`，随机势独立且均匀分布于 `[-h, h]` 时，证明几乎必然谱为 `[-4-h, 4+h]`。 | [题面](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [证明](data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [检查结果](data/proofs/openai_planar_anderson_spectrum/verification.json) · [研究过程](data/proofs/openai_planar_anderson_spectrum/process.json) |
| **树上三状态模型的超临界重构** | 在题目给定的超临界条件下，证明正则树与泊松树的重构优势趋于正极限。 | [题面](data/proofs/openai_three_state_supercritical/Challenge.lean) · [证明](data/proofs/openai_three_state_supercritical/Submission.lean) · [检查结果](data/proofs/openai_three_state_supercritical/verification.json) · [研究过程](data/proofs/openai_three_state_supercritical/process.json) |
| **Snaky 获胜策略** | 面对合法应手，严格证明在 35 次 Maker 落子内完成 Snaky，并保持局面合法。 | [题面](data/proofs/openai_snaky_conditional/Challenge.lean) · [证明](data/proofs/openai_snaky_conditional/Submission.lean) · [检查结果](data/proofs/openai_snaky_conditional/verification.json) · [研究过程](data/proofs/openai_snaky_conditional/process.json) |

👉 **[点击查看全部 26 条证明与检查记录](#证明与检查结果)**。

## 研究合作

我们向数学界与 AI for Math 领域的学者发出诚挚邀请，欢迎开展以下方向的研究合作：

* **🎓 面向数学研究者**：欢迎带着手头正在攻关的问题、初步思路或尚未完成的 Lean 证明前来交流。我们可以依托 TheoremOS 共同核对定义与假设、推演多条证明路线、排查缺失的关键辅助引理，并评估已有结论能否高效复用，借助 AI 加速研究进程。
* **🤖 面向数学 Agent 研究同行**：欢迎共同探讨搜索策略、上下文选择与多智能体协作机制。系统底层的**执行、结果检查、搜索调度、上下文管理和角色分工均为高度解耦的可替换模块化设计**，并支持通过 CLI 直接运行实验——便于在固定题目、模型、环境和预算的条件下，严谨地横向对比不同算法与方法。

💌 **联系方式**：有意合作请发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)**，欢迎附上题目来源或 Lean 陈述、已尝试的方法以及希望共同探讨的问题。公开的学术讨论与功能建议，欢迎随时 **[提交 GitHub Issue](https://github.com/LikC1606/theorem-os-site/issues/new)**。

## 内测与使用

TheoremOS 目前通过邮箱白名单机制开放研究内测。**内测期间，TheoremOS 平台本身完全免费**，用户仅需使用自己的 API Key 支付大模型调用费用，即可使用整套协同研究系统。

> 💡 **免 Key 在线浏览**：若想先了解系统处理数学难题的运行与推演过程，无需配置 API Key，可直接浏览 **[证明档案库](https://theoremos.top/archive.html)** 或观看 **[示例实机回放](https://theoremos.top/#demo)**。

**内测接入流程：**
1. **申请内测**：通过 **[GitHub Issue 申请通道](https://github.com/LikC1606/theorem-os-site/issues/new?template=early-access.yml)** 简要说明研究用途（可选附公开题目或 Lean 陈述链接）；也可直接发邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 申请。*(安全提示：公开 Issue 中请勿填写 API Key 或个人隐私信息)*
2. **确认白名单权限**：审核通过后，按回复指引通过邮件确认登录邮箱；加入白名单后，使用邮箱验证码即可登录 **[app.theoremos.top](https://app.theoremos.top/)** 云端工作台。
3. **接入模型服务**：连接 OpenAI 或兼容 Responses API 的大模型服务，填写自己的 API Key，选择推理模型并设置形式化与证明预算。
4. **提交任务与核查**：直接提交自然语言、$\TeX$ 或已有的 Lean 题目与未完成证明，在线核对 Lean 陈述，实时查看证明推演过程与模型用量，并可随时一键下载源码、检查报告和复查文件。

## 证明与检查结果

### Lean-Eval：10 份官方通过的证明

<details>
<summary><b>📂 点击展开：查看全部 10 份通过官方评测的证明</b></summary>

| 证明 | 领域 | 官方结果 |
| --- | --- | --- |
| [群环中的非平凡单位：单位猜想反例](accepted/annals_unit_conjecture/) | 代数 | [🏅 #1246 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| [Rademacher 型与 Enflo 型的一致性](accepted/annals_rademacher_enflo_type/) | 泛函分析 | [🏅 #2115 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| [固定夹角的等角线](accepted/annals_equiangular_lines_fixed_angle/) | 离散几何 | [🏅 #2135 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |
| [分数期望阈值](accepted/annals_fractional_expectation_thresholds/) | 概率组合 | [🏅 #2141 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2141#issuecomment-6197783762) |
| [Dimitrov 的代数整数 house 下界](accepted/dimitrov/) | 代数数论 | [🏅 #2143 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [Hopf–Rinow 定理](accepted/hopf_rinow/) | 黎曼几何 | [🏅 #2143 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [向日葵引理的改进界](submitted/annals_improved_bounds_sunflower_lemma/) | 组合数学 | [🏅 #2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [Lorentzian 多项式的闭包刻画](submitted/annals_lorentzian_polynomials/) | 代数组合 | [🏅 #2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [纸带 Möbius 环的长宽比下界](submitted/annals_optimal_moebius/) | 几何 | [🏅 #2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [代数整数：λ_SSS 的上界](submitted/annals_algebraic_integers/) | 代数数论 | [🏅 #2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |

模型与来源信息见 [accepted.json](accepted/accepted.json) 和 [submitted.json](submitted/submitted.json)。最后四项在[提交 #2144](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) 中一同通过，源码保存在 `submitted/`。

</details>

### OpenAI Math：16 条证明记录

以下 16 条证明记录已由我们运行 Lean 和原题检查程序严格复核（均公开完整研究过程），OpenAI 官方评测结果尚未确认。

<details>
<summary><b>📂 点击展开：查看全部 16 条记录的题目、证明源码、检查结果与完整研究过程</b></summary>

| 题目 | 领域 | 题面与证明 | 检查结果与研究过程 |
| --- | --- | --- | --- |
| 三状态模型在正则树与泊松树上的超临界重构 | 概率论 | [题面](data/proofs/openai_three_state_supercritical/Challenge.lean) · [证明](data/proofs/openai_three_state_supercritical/Submission.lean) | [检查结果](data/proofs/openai_three_state_supercritical/verification.json) · [研究过程](data/proofs/openai_three_state_supercritical/process.json) |
| 三角展开下匹配多面体的面对应 | 组合优化 | [题面](data/proofs/openai_triangle_face/Challenge.lean) · [证明](data/proofs/openai_triangle_face/Submission.lean) | [检查结果](data/proofs/openai_triangle_face/verification.json) · [研究过程](data/proofs/openai_triangle_face/process.json) |
| Koebe 映射及逆映射的端点不可积性 | 复分析 | [题面](data/proofs/openai_brennan_sharp/Challenge.lean) · [证明](data/proofs/openai_brennan_sharp/Submission.lean) | [检查结果](data/proofs/openai_brennan_sharp/verification.json) · [研究过程](data/proofs/openai_brennan_sharp/process.json) |
| 数值域几何与有限维压缩的辅助结果 | 泛函分析 | [题面](data/proofs/openai_hilbert_crouzeix/Challenge.lean) · [证明](data/proofs/openai_hilbert_crouzeix/Submission.lean) | [检查结果](data/proofs/openai_hilbert_crouzeix/verification.json) · [研究过程](data/proofs/openai_hilbert_crouzeix/process.json) |
| 平面 Anderson 算子的几乎必然谱 | 随机算子 | [题面](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [证明](data/proofs/openai_planar_anderson_spectrum/Submission.lean) | [检查结果](data/proofs/openai_planar_anderson_spectrum/verification.json) · [研究过程](data/proofs/openai_planar_anderson_spectrum/process.json) |
| Ising 感知器变分值的有限性 | 概率与统计物理 | [题面](data/proofs/openai_ising_finiteness/Challenge.lean) · [证明](data/proofs/openai_ising_finiteness/Submission.lean) | [检查结果](data/proofs/openai_ising_finiteness/verification.json) · [研究过程](data/proofs/openai_ising_finiteness/process.json) |
| 欧拉函数伴随定理：无种子零值情形 | 数论 | [题面](data/proofs/openai_totient_companion_zero/Challenge.lean) · [证明](data/proofs/openai_totient_companion_zero/Submission.lean) | [检查结果](data/proofs/openai_totient_companion_zero/verification.json) · [研究过程](data/proofs/openai_totient_companion_zero/process.json) |
| 归一化 Cartier 坐标回缩族的紧致性 | 代数几何与拓扑 | [题面](data/proofs/openai_cartier_chart_compactness_support/Challenge.lean) · [证明](data/proofs/openai_cartier_chart_compactness_support/Submission.lean) | [检查结果](data/proofs/openai_cartier_chart_compactness_support/verification.json) · [研究过程](data/proofs/openai_cartier_chart_compactness_support/process.json) |
| 有限同余格的彩色图判据 | 泛代数与格论 | [题面](data/proofs/openai_finite_congruence_graph/Challenge.lean) · [证明](data/proofs/openai_finite_congruence_graph/Submission.lean) | [检查结果](data/proofs/openai_finite_congruence_graph/verification.json) · [研究过程](data/proofs/openai_finite_congruence_graph/process.json) |
| 蜂窝格自由能极限的存在性 | 概率与统计物理 | [题面](data/proofs/openai_honeycomb_free_energy/Challenge.lean) · [证明](data/proofs/openai_honeycomb_free_energy/Submission.lean) | [检查结果](data/proofs/openai_honeycomb_free_energy/verification.json) · [研究过程](data/proofs/openai_honeycomb_free_energy/process.json) |
| 欧氏平面的七色着色 | 离散几何 | [题面](data/proofs/openai_plane_coloring/Challenge.lean) · [证明](data/proofs/openai_plane_coloring/Submission.lean) | [检查结果](data/proofs/openai_plane_coloring/verification.json) · [研究过程](data/proofs/openai_plane_coloring/process.json) |
| Snaky 的 35 步合法获胜策略 | 组合博弈 | [题面](data/proofs/openai_snaky_conditional/Challenge.lean) · [证明](data/proofs/openai_snaky_conditional/Submission.lean) | [检查结果](data/proofs/openai_snaky_conditional/verification.json) · [研究过程](data/proofs/openai_snaky_conditional/process.json) |
| Snaky 证书核验 | 组合博弈 | [题面](data/proofs/openai_snaky_certificate/Challenge.lean) · [证明](data/proofs/openai_snaky_certificate/Submission.lean) | [检查结果](data/proofs/openai_snaky_certificate/verification.json) · [研究过程](data/proofs/openai_snaky_certificate/process.json) |
| 六阶 Hadamard 行比值的立方纤维消去 | 线性代数 | [题面](data/proofs/openai_hadamard_cube_fiber/Challenge.lean) · [证明](data/proofs/openai_hadamard_cube_fiber/Submission.lean) | [检查结果](data/proofs/openai_hadamard_cube_fiber/verification.json) · [研究过程](data/proofs/openai_hadamard_cube_fiber/process.json) |
| 三维完备诺特正规局部复代数 | 交换代数 | [题面](data/proofs/openai_surface_cone_candidate_support/Challenge.lean) · [证明](data/proofs/openai_surface_cone_candidate_support/Submission.lean) | [检查结果](data/proofs/openai_surface_cone_candidate_support/verification.json) · [研究过程](data/proofs/openai_surface_cone_candidate_support/process.json) |
| Truffet 优化程序的有限反例 | 热带优化 | [题面](data/proofs/openai_truffet_counterexample/Challenge.lean) · [证明](data/proofs/openai_truffet_counterexample/Submission.lean) | [检查结果](data/proofs/openai_truffet_counterexample/verification.json) · [研究过程](data/proofs/openai_truffet_counterexample/process.json) |

</details>

🔍 欢迎前往 **[可视化证明档案库](https://theoremos.top/archive.html)**，直观查看系统完成每道题目的完整推演与研究过程。

## 仓库内容

本仓库公开官网页面、证明源码和研究记录；TheoremOS 运行时的源码不公开。

<details>
<summary><b>📂 仓库目录与许可</b></summary>

| 路径 | 内容 |
| --- | --- |
| [accepted/](accepted/) | 六份通过 Lean-Eval 官方评测的证明及来源记录 |
| [submitted/](submitted/) | 提交 #2144 中另外四份通过官方评测的证明 |
| [data/proofs/](data/proofs/) | 16 条 OpenAI Math 证明记录，含题目、源码、检查报告和研究过程 |
| [in-progress/](in-progress/) | 早期的 Lean 证明草稿，部分尚未完成，含有 `sorry` |
| [data/catalog.json](data/catalog.json) | 证明档案目录，含进展与检查结果链接 |
| `index.html`, `archive.html`, `feedback.html`, `en/`, `assets/` | 官网、英文页面和工作台截图 |

TheoremOS 保留运行时的所有权利。第三方字体与图标沿用 [assets/fonts/](assets/fonts/)、[assets/licenses/](assets/licenses/) 和 [lucide-LICENSE.txt](lucide-LICENSE.txt) 中随附的许可。

</details>
