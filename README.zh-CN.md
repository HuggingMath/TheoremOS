<div align="center">

<img src="assets/mark.png" alt="" width="64" height="64">

<h1>TheoremOS</h1>

<p><strong>与数学家协作的 AI 数学研究系统。</strong></p>
<p>一起探索证明路线、补齐辅助引理，用 Lean 核查证明。</p>

<p>
  <a href="https://theoremos.top/">产品官网</a> ·
  <a href="https://theoremos.top/#start"><strong>申请研究内测</strong></a> ·
  <a href="#与数学家怎样协作">协作方式</a> ·
  <a href="#研究合作">研究合作</a> ·
  <a href="https://theoremos.top/archive.html">证明档案</a> ·
  <a href="README.md">English</a>
</p>

</div>

TheoremOS 是一套与数学家协作的 AI 数学研究系统。数学家提出问题、提供思路并判断方向；系统帮助检索已有结果、尝试证明路线、证明辅助引理，并用 Lean 检查证明。

从一个思路到完整证明，往往还要查已有结论、补齐辅助引理，再把论证写成 Lean 能检查的代码。TheoremOS 会保存尝试过的路线、Lean 的反馈和未完成的步骤，方便研究者继续推敲。

系统从 DeepScientist 的数学证明部分发展而来。你可以输入自然语言、TeX 或已有的 Lean 题目与未完成的证明，选择模型和研究预算，查看过程，并下载源码和检查报告。在线使用无需在本机安装 Lean 或 Docker。

本仓库公开了 26 条证明记录：[10 份通过 Lean-Eval 官方评测的证明](#lean-eval10-份官方通过的证明)和 [16 条 OpenAI Math 证明记录](#openai-math16-条证明记录)。这些结果来自 TheoremOS 及其前身 DeepScientist / DeepScientist Math。

<a href="https://theoremos.top/#start">
  <picture>
    <source media="(max-width: 640px)" srcset="assets/workbench-mobile.png">
    <img src="assets/workbench-desktop.png" alt="TheoremOS 中文工作台的自然语言入口，展示题目输入、模型设置以及形式化与证明预算" width="1440">
  </picture>
</a>

<p align="center"><sub>题目输入界面 · <a href="assets/workbench-full-desktop.png">查看完整截图</a></sub></p>

## 与数学家怎样协作

数学家可以带着一个问题、初步思路或未完成的 Lean 证明开始。自然语言或 TeX 输入会先转成 Lean 定义和定理陈述。系统检查编译，再把 Lean 陈述译回通常的数学语言，帮助研究者核对是否准确表达了原题。题意核对与证明检查的结果会分别展示。

遇到证明缺口时，系统可以查找已有结果，也可以先证明一个辅助引理，或尝试其他路线。研究者可以查看此前的方法、Lean 报错和模型用量，调整思路，也可以稍后恢复任务，接着研究。

系统可以独立尝试，也支持分工协作，由不同角色负责规划、检索、编写 Lean 证明和审阅，同时探索不同路线。完整题目的证明会由独立的 Lean 检查程序核对。

通过 Lean 检查的定理和引理可以存入知识库，按类型、前提和来源查找；用于其他问题时，会在对应的 Lean 环境中重新检查。

## 代表案例

| 案例 | 结论 | 证明与检查结果 |
| --- | --- | --- |
| [Hopf–Rinow](accepted/hopf_rinow/) | 在题目给定的流形条件下，测地完备与度量完备等价。 | [证明](accepted/hopf_rinow/Submission.lean) · [官方通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| 平面 Anderson 算子谱 | 当 `h > 0`，随机势独立且均匀分布于 `[-h, h]` 时，几乎必然谱为 `[-4-h, 4+h]`。 | [题面](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [证明](data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [检查结果](data/proofs/openai_planar_anderson_spectrum/verification.json) · [研究过程](data/proofs/openai_planar_anderson_spectrum/process.json) |
| 树上三状态模型的超临界重构 | 在题目给定的超临界条件下，正则树与泊松树的重构优势趋于正极限。 | [题面](data/proofs/openai_three_state_supercritical/Challenge.lean) · [证明](data/proofs/openai_three_state_supercritical/Submission.lean) · [检查结果](data/proofs/openai_three_state_supercritical/verification.json) · [研究过程](data/proofs/openai_three_state_supercritical/process.json) |
| Snaky 获胜策略 | 面对合法应手，在 35 次 Maker 落子内完成 Snaky，并保持局面合法。 | [题面](data/proofs/openai_snaky_conditional/Challenge.lean) · [证明](data/proofs/openai_snaky_conditional/Submission.lean) · [检查结果](data/proofs/openai_snaky_conditional/verification.json) · [研究过程](data/proofs/openai_snaky_conditional/process.json) |

[查看全部 26 条证明记录](#证明与检查结果)。

## 研究合作

欢迎数学家带着正在研究的问题、已有思路或未完成的 Lean 证明来交流。我们可以一起核对定义与假设、讨论证明路线，分析还缺哪些引理，以及已有结果能否复用。

也欢迎数学 Agent 研究者一起研究搜索、上下文选择和协作策略。系统把执行、结果检查、搜索调度、上下文管理和角色分工分别做成可替换模块，便于在相同的题目、模型、环境和预算下比较方法。也可通过 CLI 运行实验。

合作请联系 [liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)，附上题目来源或 Lean 陈述、已经尝试的方法，以及希望一起研究的问题。公开讨论和产品反馈可[提交 Issue](https://github.com/LikC1606/theorem-os-site/issues/new)。

## 内测与使用

目前通过邮箱白名单开放内测。内测期间平台免费，模型调用由你的 API 账户付费。

1. [申请内测](https://github.com/LikC1606/theorem-os-site/issues/new?template=early-access.yml)，说明研究用途即可，可选附公开题目或 Lean 声明链接。也可发邮件至 [liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn) 私下申请。
2. 审核后，按回复指引通过邮件私下确认登录邮箱。获准加入白名单后，用邮箱验证码登录 [app.theoremos.top](https://app.theoremos.top/)。
3. 连接 OpenAI 或兼容 Responses API 的服务，填写自己的 API Key，并设置形式化与证明预算。
4. 提交自然语言、TeX 或 Lean 题目，核对 Lean 陈述，查看证明过程，下载源码、检查报告和复查所需的文件。

Issue 公开显示，请勿填写 API Key 或个人联系方式。

也可以先浏览[证明档案](https://theoremos.top/archive.html)或查看[示例回放](https://theoremos.top/#demo)，无需 API Key。

## 证明与检查结果

### Lean-Eval：10 份官方通过的证明

<details>
<summary>查看全部 10 份证明与官方评测结果</summary>

| 证明 | 领域 | 官方结果 |
| --- | --- | --- |
| [群环中的非平凡单位：单位猜想反例](accepted/annals_unit_conjecture/) | 代数 | [#1246 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| [Rademacher 型与 Enflo 型的一致性](accepted/annals_rademacher_enflo_type/) | 泛函分析 | [#2115 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| [固定夹角的等角线](accepted/annals_equiangular_lines_fixed_angle/) | 离散几何 | [#2135 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |
| [分数期望阈值](accepted/annals_fractional_expectation_thresholds/) | 概率组合 | [#2141 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2141#issuecomment-6197783762) |
| [Dimitrov 的代数整数 house 下界](accepted/dimitrov/) | 代数数论 | [#2143 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [Hopf–Rinow 定理](accepted/hopf_rinow/) | 黎曼几何 | [#2143 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| [向日葵引理的改进界](submitted/annals_improved_bounds_sunflower_lemma/) | 组合数学 | [#2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [Lorentzian 多项式的闭包刻画](submitted/annals_lorentzian_polynomials/) | 代数组合 | [#2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [纸带 Möbius 环的长宽比下界](submitted/annals_optimal_moebius/) | 几何 | [#2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |
| [代数整数：λ_SSS 的上界](submitted/annals_algebraic_integers/) | 代数数论 | [#2144 · 通过](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) |

模型与来源信息见 [accepted.json](accepted/accepted.json) 和 [submitted.json](submitted/submitted.json)。最后四项在[提交 #2144](https://github.com/leanprover/lean-eval-submissions/issues/2144#issuecomment-6222767100) 中一同通过，源码保存在 `submitted/`。

</details>

### OpenAI Math：16 条证明记录

我们用 Lean 和原题的检查程序复核了这 16 条记录；OpenAI 官方评测结果尚未确认。

<details>
<summary>查看全部 16 条记录的题目、证明与检查结果</summary>

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

也可在[证明档案](https://theoremos.top/archive.html)中查看研究过程。

## 仓库内容

本仓库公开官网、证明源码和研究记录。TheoremOS 运行时的源码不公开。

<details>
<summary>仓库目录与许可</summary>

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
