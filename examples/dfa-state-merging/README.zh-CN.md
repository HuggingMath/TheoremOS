# 合并自动机状态并保持识别语言

[English](README.md)

给定一台确定性有限自动机和几对待合并状态。合并一对状态后，它们读入同一个符号所到达的状态也必须合并。同时，同一组里的状态要对空输入给出相同的接受或拒绝结果。

示例把每个输入符号视为作用在状态上的一元运算，调用档案的 `eqvGenTranslate_compatible`，证明待合并状态对生成的等价关系在每种转移下都保持。Lean 定理 `merge_safe_iff` 证明，生成的每组状态具有一致的接受性，当且仅当每对待合并状态都接受完全相同的后续输入。`merged_accepts` 进一步证明，按这些等价类构造的自动机识别原来的语言。[归档引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_finite_congruence_graph/Submission.lean#L222)

示例机器有四个可达状态，用两位记录状态。读到 1 时翻转奇偶位，读到 0 时翻转另一位。机器只在已经读到偶数个 1 时接受。把两个偶数状态合并后，读到 1 的转移会使两个奇数状态也合并。Lean 验证了合并结果恰有两个状态，且识别语言不变。

判据、商自动机和具体示例都已在固定版本的 Lean 和 Mathlib 下通过检查。[本地复核命令](README.md#check-locally) · [Lean 源码](DFAStateMerging.lean)
