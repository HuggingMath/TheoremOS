# 真实研究案例：平面 Anderson 算子的几乎必然谱

[English](CASE-STUDY.md) · [返回中文主页](../README.zh-CN.md)

在现代数学研究中，将分析学或概率论中的连续极限、测度论细节与算子谱理论完全形式化，通常需要耗费大量精力处理繁琐的底层引理。TheoremOS 被设计为与数学家协作的 AI 数学研究系统：支持自然语言、$`\TeX`$ 与 Lean 4 输入，负责检索文献背景、将核心目标分解为可验证的中间引理、探索不同证明路径，并对提交的完整证明运行独立的 Lean 内核检查。

本文通过公开档案中的平面随机薛定谔算子（二维 Anderson 模型）谱刻画问题，展示系统如何完成从算子构造、概率测度交换到近似特征向量估计的完整形式化证明。读者可直接核查全部源码与机器检查记录：[交互式证明档案](https://theoremos.top/archive.html#proof=openai_planar_anderson_spectrum)与[探索过程档案](https://theoremos.top/archive.html#proof=openai_planar_anderson_spectrum&tab=process)。

## 问题陈述与形式化目标

考虑二维整数格点 $`\mathbb{Z}^2`$ 上的复希尔伯特空间 $`\ell^2(\mathbb{Z}^2)`$。紧束缚平面 Anderson 算子 $`H = \Delta + V`$ 作用在序列 $`\psi \in \ell^2(\mathbb{Z}^2)`$ 上，其逐点定义为四个最近邻平移之和加上实值随机势乘法：

$$(H\psi)(x) = \psi(x+e_1) + \psi(x-e_1) + \psi(x+e_2) + \psi(x-e_2) + V(x)\psi(x)$$

其中 $`e_1=(1,0), e_2=(0,1)`$。设实值随机场 $`\lbrace V(x)\rbrace _{x \in \mathbb{Z}^2}`$ 坐标独立，且每个坐标同分布于区间 $`[-h, h]`$（$`h > 0`$）上的均匀分布。目标是证明 $`H`$ 的谱几乎必然为闭区间 $`[-4-h, 4+h]`$。

在 [Challenge.lean](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean) 给出的正式命题 `OAI.PlanarAnderson.anderson_spectrum_ae` 中，结论并非仅写出最终区间，而是要求在同一测度框架下同时证明：对几乎处处的样本点 $`\omega`$，满足上述逐点公式的有界线性算子 $`H(\omega)`$ 存在、算子本身是自伴的（`IsSelfAdjoint`），且其复谱 $`\sigma_{\mathbb{C}}(H(\omega))`$ 精确等于 $`[-4-h, 4+h]`$ 的复嵌入。

## 论证结构与 Lean 4 实现

在非形式化文献中，该定理通常由算子范数界给出谱的上界，再借由 Weyl 近似特征值判据（近似特征向量论证）与独立同分布势的近常数块出现性质给出下界。将这一论证转化为无公理漏洞的 Lean 4 代码，需要明确填补测度可数交与离散拉普拉斯边界面估计的每一处细节。

在 [Submission.lean](../data/proofs/openai_planar_anderson_spectrum/Submission.lean)（共 1,454 行）中，系统通过以下五个核心阶段完成了证明：

| 数学工作阶段 | 核心定义与引理（点击查看源码） | 形式化解决的具体内容 |
| :--- | :--- | :--- |
| 1. 算子构造与谱上界 | [`anderson_operator_exists_selfAdjoint`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L224)<br>`anderson_spectrum_subset` | 将算子分解为邻接算子 `adjacencyCLM` 与有界乘法算子 `mulCLM hv` 之和，证明自伴性及 $`\Vert H\Vert  \le 4+h`$，结合自伴算子谱的实数性导出 $`\sigma(H) \subseteq [-4-h, 4+h]`$。 |
| 2. 任意大近常数块出现 | [`constant_block_occurrence`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L485) | 对给定目标值 $`c \in [-h,h]`$、误差 $`\varepsilon>0`$ 与尺寸 $`N`$，利用不相交有限方块的独立性与均匀分布正概率，证明几乎必然存在某平移方块使势函数与 $`c`$ 的偏差小于 $`\varepsilon`$。 |
| 3. 可数稠密集与零测集交换 | [`ae_blocks_simultaneous`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L921) | 通过有理数逼近与可数交，将“每个常数分别几乎必然出现”提升为“在同一个全测度事件上，同时对所有目标常数、尺度和精度出现近常数块”。 |
| 4. 截断平面波与谱下界 | [`finite_box_approx_eigenvector`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1206)<br>[`spectrum_lower_of_blocks_pos`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1252) | 在大方块内构造归一化截断平面波 $`u`$，精细控制方块边界的跃迁误差与内部势偏差，使 $`\Vert (H-\lambda I)u\Vert `$ 任意小，再由 [`approx_eigenvalue_mem_spectrum`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L281) 推出 $`\lambda \in \sigma(H)`$。 |
| 5. 主定理汇合 | [`anderson_spectrum_ae`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1446) | 严格保持原题类型签名，调用辅助定理 `exact anderson_spectrum_ae_sorry_free hh` 汇合上下包含关系，完成定理闭环。 |

### 关键形式化难点：量词与“几乎处处”的交换

此证明中最具代表性的形式化难点在于第 3 阶段（[`ae_blocks_simultaneous`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean#L921)）。在纸面证明中，人们容易由“对任意 $`c \in [-h,h]`$，以概率 1 存在近似常数 $`c`$ 的方块”直接过渡到整个区间的谱包含。但在测度论中，$`\forall c \in [-h,h],\, \mathbb{P}(\Omega_c)=1`$ 不能直接交换为 $`\mathbb{P}(\bigcap_{c \in [-h,h]} \Omega_c)=1`$，因为不可数个零测集的并集未必可测或仍为零测集。

`Submission.lean` 通过引入可数有理网格解决了这一问题：首先对所有满足 $`c' \in [-h,h]`$、$`\varepsilon' > 0`$ 的有理数对与整数方块尺寸 $`(c', \varepsilon', N) \in \mathbb{Q} \times \mathbb{Q} \times \mathbb{N}`$ 取可数交，构造出一个统一的事件 $`\Omega_0`$（满足 $`\mathbb{P}(\Omega_0)=1`$）；随后在固定样本 $`\omega \in \Omega_0`$ 的前提下，对任意实数势值 $`c \in [-h,h]`$ 与任意精度 $`\varepsilon > 0`$，选取充分接近的有理数 $`c' \in [-h,h]`$ 与有理精度 $`\varepsilon' > 0`$，用三角不等式将实数目标归结到已构造的有理网格上。同样地，在第 4 阶段构造截断平面波时，代码对二维有限方块内部的本征方程相消与边界项作了逐项展开，证明边界误差随方块增大趋于零，避免了在形式化环境中依赖模糊的渐近记号。

## 研究过程记录与人机协作视角

系统的[探索过程档案](https://theoremos.top/archive.html#proof=openai_planar_anderson_spectrum&tab=process)与 [`process.json`](../data/proofs/openai_planar_anderson_spectrum/process.json) 完整保留了任务分解图。除最终走通的有限方块与近似特征向量主线外，公开记录中也保留了 `constant_potential_spectrum`、`constant-box-bridge`、`weyl-fallback` 等未完成的替代路线（处于 `blocked` 或 `pending` 状态），研究者可将它们与最终采纳的证明路径对照阅读。

本案例归档记录含历史续跑（事件时间戳自 2026-10-28 起），当前接受运行未见外部数学编辑记录。如果在自己的日常研究中使用 TheoremOS，数学家可以在这一分解结构上直接介入：例如在系统展开证明前核对算子定义与测度假设，在多条探索分支出现时判断哪条分析路线更值得继续分配预算，或在某一中间引理受阻时直接提供关键不等式提示。

## 独立检查与核验结果

归档检查记录 [`verification.json`](../data/proofs/openai_planar_anderson_spectrum/verification.json) 显示，本证明已通过项目运行的独立 Lean 内核检查与原题比较器（comparator）校验：

* **检查状态**：`status = evaluated_passed`，`kernelStatus = kernel_verified`，`comparatorExitCode = 0`，`reviewStatus = accepted`。
* **校验输出**：包含 `Lean default kernel accepts the solution` 与 `Your solution is okay!`。
* **公理依赖**：`process.json` 的 `runs[0].review.summary` 记录显示，最终目标与辅助定理仅依赖 Lean 标准公理 `propext`、`Classical.choice` 与 `Quot.sound`，不含 `sorryAx` 或任何新增自定义公理。

> **评测状态说明**：以上结果为本项目运行的独立 Lean 内核及原题 comparator 检查通过；**OpenAI 官方评测结果尚未确认**。

<details>
<summary>档案文件与哈希校验详情</summary>

* 原题模板（含题面占位 `sorry`）：[`Challenge.lean`](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean)
* 最终完整证明：[`Submission.lean`](../data/proofs/openai_planar_anderson_spectrum/Submission.lean)（SHA-256: `2fd7e2d1c71eff673ce58cd82f694526f9d6ed0a4ace42f800b159b26482cfc7`，与检查记录一致）
* 机器核查记录：[`verification.json`](../data/proofs/openai_planar_anderson_spectrum/verification.json)
* 运行与分解记录：[`process.json`](../data/proofs/openai_planar_anderson_spectrum/process.json)

</details>

## 相关资源与进一步探索

* **原始档案文件**：[题面 Challenge.lean](../data/proofs/openai_planar_anderson_spectrum/Challenge.lean) · [完整证明 Submission.lean](../data/proofs/openai_planar_anderson_spectrum/Submission.lean) · [检查记录 verification.json](../data/proofs/openai_planar_anderson_spectrum/verification.json) · [过程档案 process.json](../data/proofs/openai_planar_anderson_spectrum/process.json)
* **交互式浏览**：[中文证明档案](https://theoremos.top/archive.html#proof=openai_planar_anderson_spectrum) · [探索过程视图](https://theoremos.top/archive.html#proof=openai_planar_anderson_spectrum&tab=process)
* **开始使用与复核**：阅读[首次使用图文教程](GETTING-STARTED.zh-CN.md)了解如何在云端工作台发起研究，或参考[证明复核指南](VERIFY.zh-CN.md)在本地重跑检查。
* **研究合作**：关于内测权限说明请参阅 [`ACCESS.md`](ACCESS.md)，学术与研究合作请联系 `liuzhenhao@westlake.edu.cn`。
