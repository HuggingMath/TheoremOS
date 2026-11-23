# 在新题目里复用归档证明

[English](PROOF-REUSE.md) · [TheoremOS](../README.zh-CN.md)

TheoremOS 的一位维护者使用公开档案发起了下面的复用验证。Codex 编写下游 Lean 文件，并按示例记录的 Lean 和 Mathlib 版本运行检查。这些示例都可以在本地复核，无需 TheoremOS 账号或模型密钥。

- **谱理论。** 从 Anderson 证明中调用有限方块引理，求二维格点上确定性阶跃势的谱。当两侧贡献的谱区间相接或重叠时，可以得到整个谱。[阶跃势示例](../examples/anderson-step-potential/README.zh-CN.md)
- **代数数论。** 从 Dimitrov 的下界导出由数域次数决定的门槛。若一个非零代数整数的所有共轭模长都严格小于该门槛，它就是单位根。[单位根示例](../examples/dimitrov-degree-bound/README.md)
- **组合优化**示例调用三角展开定理，把原有边上的预算约束和目标函数转到展开图匹配多面体的对应面上。任意预算下，两边能达到的成本值相同。[带预算的匹配示例](../examples/triangle-weighted-matching/README.zh-CN.md)
- **实分析**示例调用 Hopf–Rinow 档案的辅助引理。若区间上的弱导数由实轴上的连续函数给出，局部可积的函数几乎处处等于弱导数的积分加一个常数。若这个函数本身也连续，任意两个内点间的增量就是相应区间上的积分。[弱形式的微积分基本定理示例](../examples/weak-fundamental-theorem/README.zh-CN.md)
- **距离几何**示例调用等角直线档案中实现 Gram 矩阵的引理，从一张平方距离表判定能否在指定维数的欧氏空间放下这些点，并验证边长为 3、4、5 的三角形至少需要二维。[欧氏距离表示例](../examples/distance-geometry/README.zh-CN.md)
- **编码理论**示例调用 Hadamard 档案中按行比值分组的求和引理。当六相位矩阵及其逐项平方都为复 Hadamard 矩阵时，两个不同的二元投影码字至少相差三位，因此至多一位错误时，投影码字可以唯一确定。[六相位码示例](../examples/six-phase-code/README.zh-CN.md)
- **自动机理论**示例复用同余引理，给出合并状态而保持识别语言的判据。一个有四个可达状态的奇偶性自动机，合并后只需两个状态就能识别同一种语言。[状态合并示例](../examples/dfa-state-merging/README.zh-CN.md)
- **统计推断**示例把树重构引理用到等先验分类。若对每种观测，至多一类的似然高于混合似然，可用两类观测分布的总变差给最优准确率做下界。一个三类、两种观测结果的实验恰好达到这个下界。[多类假设检验示例](../examples/multiclass-hypothesis-testing/README.zh-CN.md)

## 已在两份归档证明里使用的同一条引理

两份三状态树重构证明都调用了 `pmfTV_le_card_mul_reconAdvantage`。若两种根状态对应的叶端观测分布的总变差至少 $\delta$，在三状态情形下，该引理就把它转成至少 $\delta/3$ 的重构优势。两份档案里的引理源文件字节相同，原题比较器记录的退出码均为 `0`。[引理定义](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/Submission/Library/TheoremOS/Probability/TreeReconstruction.lean#L276) · [正则树与泊松树的调用](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_supercritical/Submission.lean#L1004) · [另一份树信道证明的调用](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/Submission.lean#L1131) · [检查记录一](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_supercritical/verification.json) · [检查记录二](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/verification.json)

该共享模块的原始文件及获授权的适配版本见对应的 AGPL-3.0-only 说明。[模块授权](https://github.com/HuggingMath/theorem-os/blob/7f68904e67edea7cef624b35371962f863b92333/resources/theorem-os-library/REDISTRIBUTION.md)

如果你把档案里的结论用到了自己的研究或课程里，欢迎分享原题、用到的声明和你得到的结果。有 Lean 代码时，附上可公开的源码和检查记录，方便下一位读者从那里接着做。[分享使用记录](https://github.com/HuggingMath/TheoremOS/issues/new?template=question.yml)
