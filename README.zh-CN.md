<div align="center">

<img src="assets/mark.png" alt="" width="64" height="64">

<h1>TheoremOS</h1>

<p><strong>重塑前沿数学探索范式的 AI 协同研究系统 · 数学家的智能推演引擎与形式化副驾驶</strong></p>
<p>全景协同检索已有结论 · 多路并发探索证明路线 · 强力攻坚补齐辅助引理 · Lean 引擎严密核查证明</p>

<p>
  <a href="https://theoremos.top/">🌐 产品官网</a> ·
  <a href="https://theoremos.top/#start"><strong>🚀 立即申请研究内测</strong></a> ·
  <a href="#与数学家怎样协作">核心引擎与范式</a> ·
  <a href="#研究合作">深度研究合作</a> ·
  <a href="https://theoremos.top/archive.html">📜 殿堂级证明档案</a> ·
  <a href="README.md">English</a>
</p>

</div>

**TheoremOS 是一套旨在深度解放数学家创造力、专为攻克高难度数学问题而生的革命性 AI 协同研究系统。** 在这场改变游戏规则的“人机共创”中，人类数学家稳坐统帅之位——提出核心问题、注入关键直觉并领航宏观研究方向；TheoremOS 则化身为不知疲倦、按预算精准调度的“全能数字学术搭档”，强力接管繁琐的已有结论检索、多维证明路线探索与底层辅助引理攻坚，并依托 Lean 引擎对最终证明进行绝对严密的机器核查。

系统彻底击碎了形式化工具极高的工程壁垒：研究者只需直接带入自然语言、$\TeX$ 手稿，或已有的 Lean 题目与未完成的证明，即可享受**全流程云端丝滑运行，彻底告别本地繁琐的 Lean 环境配置与 Docker 部署，真正实现“开箱即用，专注思考”**。在硬核攻坚过程中，系统将化身全景记录仪，完整留存尝试过的每一条探索路线、每一处 Lean 编译报错以及未完成的步骤，支持保存进度并在稍后无缝恢复任务，让研究者能够随时俯瞰全局推演脉络、从容调优学术战略。

> 🏆 **硬核实战战绩**：TheoremOS 的强大攻坚实力已获实战检验！本仓库重磅公开了系统攻克的 **26 条高难度前沿数学证明记录**，横跨代数数论、黎曼几何、泛函分析与统计物理等硬核领域，直接斩获 **[10 份通过 Lean-Eval 官方权威评测的证明](#lean-eval10-份官方通过的证明)**，并强势拿下 **[16 条极具挑战的 OpenAI Math 证明记录](#openai-math16-条证明记录)**！

<a href="https://theoremos.top/#start">
  <picture>
    <source media="(max-width: 640px)" srcset="assets/workbench-mobile.png">
    <img src="assets/workbench-desktop.png" alt="TheoremOS 中文工作台的自然语言入口，展示题目输入、模型设置以及形式化与证明预算" width="1440">
  </picture>
</a>

<p align="center"><sub>云端智能工作台入口 · <a href="assets/workbench-full-desktop.png">点击查看高清完整工作流截图</a></sub></p>

## 与数学家怎样协作

TheoremOS 深度解构并升华了数学研究的真实工作流，打造出极致高效、全透明的人机协同闭环：

* **🔄 跨模态双向互译与严谨题意核对**：当输入自然语言或 $\TeX$ 手稿时，系统会先将其转化为形式化的 Lean 定义和定理陈述；在底层编译检查通过后，再将 Lean 陈述**逆向译回直观的数学语言，供研究者精准核对原意**。系统将“题意核对”与后续的“证明检查”清晰分离展示，由人类专家与机器共同把关，确保研究起点固若金汤。
* **🧠 多角色协同矩阵与多路线并行探索**：在寻找证明时，系统绝非盲目试错——既支持单点强力突破，也能按**规划、检索、编写 Lean 证明和审阅**进行精细化分工协作，并行探索多条潜在证明路线。一旦遭遇证明缺口，系统会主动检索相关结果、先行尝试攻克辅助引理，或果断切换其他备选路线，展开全方位、立体式的推演攻坚。
* **🔍 上帝视角的全透明掌控与独立核查**：拒绝“黑盒”盲猜！整个研究过程对学者完全透明开放。研究者可随时检视此前试过的方法、精准定位 Lean 的具体报错并监控模型算力用量，据此随时注入人类专家的灵光一闪，精准调整方向或补充新思路。完整题目的最终证明均由独立的 Lean 检查程序严格核对。
* **🏛️ 高价值的形式化知识库沉淀与复用**：通过 Lean 检查的定理和辅助引理均可沉淀存入知识库，支持按类型、前提和来源进行高效的结构化查找；当把这些宝贵成果跨课题复用于其他问题时，系统还会在对应的 Lean 环境中重新进行严格检查，让每一次学术突破都成为后续研究的坚实基石。

## 代表案例

从经典几何定理到前沿物理数学模型，TheoremOS 已在多个核心数学分支的极限挑战中，展现出令人惊叹的协同攻坚能力：

| 攻克案例 | 核心数学结论 | 源码、核查与全景推演记录 |
| --- | --- | --- |
| **[Hopf–Rinow 定理](accepted/hopf_rinow/)** | 在题目给定的流形条件下，严密证明测地完备与度量完备等价。 | [Lean 证明](accepted/hopf_rinow/Submission.lean) · [🏅 官方权威通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| **平面 Anderson 算子谱** | 当 `h > 0`，随机势独立且均匀分布于 `[-h, h]` 时，证明几乎必然谱为 `[-4-h, 4+h]`。 | [题面](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [证明](data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [检查结果](data/proofs/openai_planar_anderson_spectrum/verification.json) · [研究过程](data/proofs/openai_planar_anderson_spectrum/process.json) |
| **树上三状态模型的超临界重构** | 在题目给定的超临界条件下，证明正则树与泊松树的重构优势趋于正极限。 | [题面](data/proofs/openai_three_state_supercritical/Challenge.lean) · [证明](data/proofs/openai_three_state_supercritical/Submission.lean) · [检查结果](data/proofs/openai_three_state_supercritical/verification.json) · [研究过程](data/proofs/openai_three_state_supercritical/process.json) |
| **Snaky 获胜策略** | 面对合法应手，严格证明在 35 次 Maker 落子内完成 Snaky，并保持局面合法。 | [题面](data/proofs/openai_snaky_conditional/Challenge.lean) · [证明](data/proofs/openai_snaky_conditional/Submission.lean) · [检查结果](data/proofs/openai_snaky_conditional/verification.json) · [研究过程](data/proofs/openai_snaky_conditional/process.json) |

👉 **[震撼不止于此，立即检阅全部 26 条硬核证明记录](#证明与检查结果)**。

## 研究合作

独行快，众行远。我们向全球数学界与 AI for Math 领域的学者发出诚挚邀请，携手探索人类理性与机器智能的边界：

* **🎓 面向数学研究者（带上您的难题来！）**：极其欢迎带着手头正在攻关的问题、初步思路或尚未完成的 Lean 证明前来深度交流！我们可以依托 TheoremOS 一起核对定义与假设、深入推演多条证明路线，精准排查还缺少哪些关键辅助引理，并评估已有结论能否高效复用，让 AI 成为您学术攻坚的强力助推器。
* **🤖 面向数学 Agent 研究同行（共建底层算法生态！）**：欢迎共同探讨搜索策略、上下文选择与多智能体协作机制的极限。系统底层的**执行、结果检查、搜索调度、上下文管理和角色分工均为高度解耦的可替换模块化设计**，并支持通过 CLI 直接运行实验——让您能够在固定题目、模型、环境和预算的严苛条件下，极其便利、严谨地横向比较不同算法与方法。

💌 **开启合作对话**：有意合作请直接发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)**，非常欢迎附上题目来源或 Lean 陈述、已经试过的方法以及希望一起研究的问题。公开的学术讨论与功能建议，也欢迎随时 **[提交 GitHub Issue](https://github.com/LikC1606/theorem-os-site/issues/new)**。

## 内测与使用

TheoremOS 目前通过邮箱白名单机制正式开放研究内测。**内测期间，TheoremOS 平台本身完全免费！** 用户仅需使用自己的 API Key 支付基础的大模型调用费用，即可畅享整套协同研究系统。

> 💡 **零门槛、免 Key 沉浸式体验**：若想先直观领略系统攻克数学难题的运行与推演过程，无需配置任何 API Key，现在即可直接浏览 **[殿堂级证明档案](https://theoremos.top/archive.html)** 或观看 **[示例实机回放](https://theoremos.top/#demo)**！

**仅需四步，即刻唤醒您的 AI 数学副驾驶：**
1. **极速申请内测**：通过 **[GitHub Issue 申请通道](https://github.com/LikC1606/theorem-os-site/issues/new?template=early-access.yml)** 简要说明研究用途（可选附公开题目或 Lean 陈述链接）；也可直接发邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 私下申请。*(安全提示：公开 Issue 中请勿填写 API Key 或个人联系方式)*
2. **确认白名单权限**：审核通过后，按回复指引通过邮件确认登录邮箱；加入白名单后，使用邮箱验证码即可一键登录 **[app.theoremos.top](https://app.theoremos.top/)** 云端工作台。
3. **自由接入顶尖模型**：无缝连接 OpenAI 或兼容 Responses API 的大模型服务，填写自己的 API Key，灵活选择推理模型并自主设置形式化与证明预算。
4. **开启协同攻坚与核查**：直接提交自然语言、$\TeX$ 或已有的 Lean 题目与未完成证明，在线精准核对 Lean 陈述，实时洞察证明推演过程与模型用量，并随时一键打包下载源码、检查报告和复查所需的文件！

## 证明与检查结果

### Lean-Eval：10 份官方通过的证明

<details>
<summary><b>📂 点击展开：检阅全部 10 份斩获官方权威评测通过的硬核证明</b></summary>

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

以下 16 条高难度挑战记录已由我们运行 Lean 和原题检查程序严格复核（完整公开全链路研究过程），OpenAI 官方评测结果尚未确认。

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

🔍 强烈推荐前往 **[可视化证明档案](https://theoremos.top/archive.html)**，身临其境地直观查看系统攻克每道难题的完整推演与研究过程！

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
