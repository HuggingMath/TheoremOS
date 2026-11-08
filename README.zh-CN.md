<div align="center">

<img src="assets/mark.png" alt="" width="64" height="64">

<h1>TheoremOS</h1>

<p><strong>面向前沿数学研究的 AI 协同系统与形式化证明平台</strong></p>
<p>双向题意核对 · 宏观路线先行验证 · 多路引理并行攻关 · 证明过程留存与成果复用</p>

<p>
  <a href="https://theoremos.top/">🌐 产品官网</a> ·
  <a href="https://theoremos.top/#start"><strong>🚀 申请研究内测</strong></a> ·
  <a href="#核心创新与系统设计">核心创新</a> ·
  <a href="#怎样支持数学研究">研究工作流</a> ·
  <a href="#代表案例">代表案例</a> ·
  <a href="#研究合作">研究合作</a> ·
  <a href="https://theoremos.top/archive.html">📜 证明档案库</a> ·
  <a href="README.md">English</a>
</p>

</div>

**TheoremOS 是一套专为攻克高难度数学问题而设计的 AI 协同研究系统。** 在研究过程中，数学家负责提出核心问题、注入直觉并把控宏观方向；TheoremOS 则根据算力预算，承担文献与结论检索、辅助引理拆解、多路径证明探索与 Lean 代码编写，并由独立的 Lean 检查程序严格核验最终证明。

系统将“题意核对”、“多角色研究协作”、“独立证明检查”与“研究记录及成果复用”整合为完整的研究闭环。研究者既可通过免本地配置 Lean 与 Docker 的云端工作台开箱即用，也可通过命令行（CLI）独立运行与开展实验。

> 🧭 **迈向“Math 2.0”的协同研究范式**：菲尔兹奖得主陶哲轩（Terence Tao）在其[《Math 2.0》博客](https://terrytao.wordpress.com/2026/10/10/math-2-0/)与 [Caltech 公开讲座讲稿](https://teorth.github.io/tao-web/slides/math-2-0-caltech-2026.pdf)（2026 年 10 月）中指出：
>
> *“The more sustainable ‘Math 2.0’ use of AI would be to strengthen all the ways in which human understanding interacts with mathematics.”*（讲稿第 23 页）\
> *（更具可持续性的 AI “Math 2.0” 用法，应当是全方位强化人类理解与数学产生交互的每一种方式。）*
>
> 他同时强调，数学探索应超越单一的解题指标（Beyond problem-solving，第 9、16 页）——探索过程中的阶段性进展与失败尝试同样具有研究价值；而建设如 Mathlib 般大型高质量的形式化数学库、将零散研究连接为持续更新的知识网络，正是“Math 2.0”的核心应用方向（第 25 页）。**TheoremOS 的设计与这一愿景高度契合：我们不做仅输出结果的黑盒解题器，而是通过严谨的题意对齐、透明的过程记录与引理级知识积累，为数学家提供可靠、可持续的协同研究工具。**

> 🏆 **研究成果与评测表现**：本仓库公开了系统完成的 **26 条高难度前沿数学证明记录**，涵盖代数数论、黎曼几何、泛函分析与统计物理等领域，其中包括 **[10 份通过 Lean-Eval 官方评测的证明](#lean-eval10-份官方通过的证明)**，以及 **[16 条经本地 Lean 与原题检查程序复核的 OpenAI Math 证明记录](#openai-math16-条证明记录)**。

<a href="https://theoremos.top/#start">
  <picture>
    <source media="(max-width: 640px)" srcset="assets/workbench-mobile.png">
    <img src="assets/workbench-desktop.png" alt="TheoremOS 中文工作台的自然语言入口，展示题目输入、模型设置以及形式化与证明预算" width="1440">
  </picture>
</a>

<p align="center"><sub>云端智能工作台入口 · <a href="assets/workbench-full-desktop.png">点击查看高清完整工作流截图</a></sub></p>

---

## 核心创新与系统设计

围绕真实的数学研究需求，TheoremOS 在**命题对齐、引理协作、知识积累与算法实验**四个维度进行了系统性设计：

| 核心维度 | 设计新意与核心做法 | 对数学研究的价值 |
| --- | --- | --- |
| **1. 题意核对与证明检查分离** | 结构化规划后生成 Lean 陈述；由独立模型在不知晓原题的情况下，仅依据编译后的形式化陈述与定义逆向回译，并与原题逐项比对。 | 辅助排查条件遗漏、定义退化等语义偏差，减少在错误命题上空耗算力。 |
| **2. 先验证整体思路、再并行攻克引理** | 固定引理类型并携带原题上下文；**先将未证引理作为临时假设检验主定理推导**，再并行证引理、按声明合并与终审。 | 避免在走不通的整体思路上深陷细节，让多项引理的并行推导与汇总条理清晰。 |
| **3. 全过程留存与跨课题引理复用** | 完整记录探索分支与报错，支持进度保存与恢复；已验证引理归档至知识索引，跨题调用时在当前环境重检。 | 保留排错经验与阶段性成果，沉淀可跨课题安全复用的领域形式化工具箱。 |
| **4. 五组件解耦的研究决策架构** | 将**执行、结果检查、搜索调度、上下文管理、职责分配**拆为源码级可替换组件，支持 CLI 固定条件跑对照实验。 | 提供清晰的实验基座，便于控制变量、横向评测不同搜索算法与协作策略。 |

### 四项核心机制详解

* **🔄 双向互译的严谨题意核对**
  在形式化研究中，“把题目写对”与“把证明写完”是两项截然不同的工作。当输入自然语言或 $\TeX$ 手稿时，系统先规划定义、假设与结论再生成 Lean 陈述；代码通过编译后并不会直接开始搜索证明，而是引入独立的逆向翻译与审核环节：**在不参考原始手稿的前提下，仅依据实际编译后的 Lean 陈述与定义**将其还原为日常数学表述，并与原题逐项比对假设、结论及量词范围。这种双向核对机制能帮助数学家直观地审视形式化代码与真实意图的出入，及时发现条件缺失或定义退化等隐蔽的语义偏差，辅助把好形式化研究的第一道关。
* **🧩 围绕主目标的引理拆解与并行合并**
  面对复杂定理，系统支持单点深度推导、多路线并行尝试以及按“规划、检索、证明编写、审阅”进行多角色分工。
  * **假定引理成立的路线预演**：拆解出的每项辅助引理均固定其 Lean 类型与依赖，同时在子任务中保留原题的完整命题与假设，帮助底层推导始终围绕原题展开。在具体引理获证前，系统可先将这些引理类型作为临时假设，用 Lean 检验它们在逻辑上是否足以推出主定理，从而先验证高层证明思路是否走得通。
  * **声明级合并与独立终审**：各分支每次交付均绑定代码版本并核查预期类型与改动声明；多个并行分支的进展按 Lean 声明进行合并（处理独立引理的并行修改，并在发现冲突时清晰报告），随后检验其对主目标的实际应用。当所有引理获证并合并为不依赖临时假设的完整证明后，最终由独立的 Lean 检查程序（及适用的原题比较器）完成终审。
* **🏛️ 透明可控的研究记录与知识索引**
  系统开放整个推演过程，完整记录尝试过的路线、编译反馈、未完成步骤与算力消耗。研究者可随时根据受阻记录调整方向，或保存进度并在后续恢复任务。同时，任何通过 Lean 检查的定理和辅助引理均可显式导入知识索引（完整保留类型签名、前提条件、源码与环境信息），支持结构化检索；在跨课题调用时，系统会在当前 Lean 环境中重新核查，验证通过后即可安全复用。
* **⚙️ 支持严谨对照的模块化实验平台**
  网页端工作台之下，TheoremOS 将底层运行逻辑拆分为五个相互独立的研究决策组件（执行、结果检查、搜索调度、上下文管理、职责分配），并与 Agent 数量解耦。研究人员无需改动系统主干，即可通过源码接口独立替换单一策略，并利用 CLI 工具在固定题目、模型、环境与预算的条件下开展严谨的对照实验。

---

## 怎样支持数学研究

在日常研究工作流中，数学家可以从四个环节切入使用 TheoremOS：

1. **对齐定义与形式化陈述**：直接提交自然语言问题、$\TeX$ 手稿或未完成的 Lean 文件，借助系统的逆向翻译与审核提示，快速校准形式化定义与假设。
2. **快速验证高层证明直觉**：提出宏观证明框架或关键中间步骤，让系统将其固定为辅助引理并先行验证“由引理推出主定理”的逻辑链条，快速判断证明思路是否可行。
3. **排查受阻点与注入直觉**：当自动探索受阻时，直观检视已尝试路线与具体编译报错，由人类研究者补充关键条件、修正引理陈述或调整拆解方式，再交由系统继续推进。
4. **沉淀课题组的形式化资产**：将研究过程中证出的技术性引理导入知识索引，供同一方向的新问题直接检索参考，免去重复造轮子的繁琐工作。

---

## 代表案例

从经典几何定理到前沿统计物理模型，TheoremOS 已在多个核心数学分支的高难度问题中展现出可靠的形式化推演能力：

| 证明案例 | 核心数学结论 | 源码、核查与完整推演记录 |
| --- | --- | --- |
| **[Hopf–Rinow 定理](accepted/hopf_rinow/)** | 在题目给定的流形条件下，严格证明测地完备与度量完备等价。 | [Lean 证明](accepted/hopf_rinow/Submission.lean) · [🏅 官方评测通过](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969) |
| **平面 Anderson 算子谱** | 当 `h > 0`，随机势独立且均匀分布于 `[-h, h]` 时，证明几乎必然谱为 `[-4-h, 4+h]`。 | [题面](data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [证明](data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [检查结果](data/proofs/openai_planar_anderson_spectrum/verification.json) · [研究过程](data/proofs/openai_planar_anderson_spectrum/process.json) |
| **树上三状态模型的超临界重构** | 在题目给定的超临界条件下，证明正则树与泊松树的重构优势趋于正极限。 | [题面](data/proofs/openai_three_state_supercritical/Challenge.lean) · [证明](data/proofs/openai_three_state_supercritical/Submission.lean) · [检查结果](data/proofs/openai_three_state_supercritical/verification.json) · [研究过程](data/proofs/openai_three_state_supercritical/process.json) |
| **Snaky 获胜策略** | 面对合法应手，严格证明在 35 次 Maker 落子内完成 Snaky，并保持局面合法。 | [题面](data/proofs/openai_snaky_conditional/Challenge.lean) · [证明](data/proofs/openai_snaky_conditional/Submission.lean) · [检查结果](data/proofs/openai_snaky_conditional/verification.json) · [研究过程](data/proofs/openai_snaky_conditional/process.json) |

👉 **[点击查看全部 26 条证明与检查记录](#证明与检查结果)**。

---

## 研究合作

我们向数学界与 AI for Math 领域的学者发出诚挚邀请，欢迎开展以下方向的研究合作：

* **🎓 面向数学研究者**：欢迎带着手头正在攻关的问题、初步思路或尚未完成的 Lean 证明前来交流。我们可以依托 TheoremOS 共同核对定义与假设、推演多条证明路线、排查缺失的关键辅助引理，并评估已有结论能否高效复用，借助 AI 加速研究进程。
* **🤖 面向数学 Agent 研究同行**：欢迎共同探讨搜索策略、上下文选择与多智能体协作机制。系统底层的执行、结果检查、搜索调度、上下文管理和职责分配均为解耦的可替换模块，并配备完整的 CLI 实验工具——欢迎基于此平台开展消融实验，共同探索不同协作模式与决策组件的实际增益。

💌 **联系方式**：有意合作请发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)**，欢迎附上题目来源或 Lean 陈述、已尝试的方法以及希望共同探讨的问题。公开的学术讨论与功能建议，欢迎随时 **[提交 GitHub Issue](https://github.com/LikC1606/theorem-os-site/issues/new)**。

---

## 内测与使用

TheoremOS 目前通过邮箱白名单机制开放研究内测。**内测期间，TheoremOS 平台本身完全免费**，用户仅需使用自己的 API Key 承担大模型调用费用，即可使用整套协同研究系统。

> 💡 **免 Key 在线浏览**：若想先了解系统处理数学难题的运行与推演过程，无需配置 API Key，可直接浏览 **[证明档案库](https://theoremos.top/archive.html)** 或观看 **[示例实机回放](https://theoremos.top/#demo)**。

**内测接入流程：**

1. **申请内测**：通过 **[GitHub Issue 申请通道](https://github.com/LikC1606/theorem-os-site/issues/new?template=early-access.yml)** 简要说明研究用途（可选附公开题目或 Lean 陈述链接）；也可直接发邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 申请。*(安全提示：公开 Issue 中请勿填写 API Key 或个人隐私信息)*
2. **确认白名单权限**：审核通过后，按回复指引通过邮件确认登录邮箱；加入白名单后，使用邮箱验证码即可登录 **[app.theoremos.top](https://app.theoremos.top/)** 云端工作台。
3. **接入模型服务**：连接 OpenAI 或兼容 Responses API 的大模型服务，填写自己的 API Key，选择推理模型并设置形式化与证明预算。
4. **提交任务与核查**：直接提交自然语言、$\TeX$ 或已有的 Lean 题目与未完成证明，在线核对 Lean 陈述，实时查看证明推演过程与模型用量，并可随时一键下载源码、检查报告和复查文件。

---

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

以下 16 条证明记录已由我们运行独立的 Lean 检查程序和原题比较器严格复核（均公开完整研究过程），OpenAI 官方评测结果尚未确认。

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

---

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
