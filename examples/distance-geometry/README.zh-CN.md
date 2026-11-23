# 判断平方距离表能否在欧氏空间实现

[English](README.md)

设 $D_{ij}$ 给出了每一对点的平方距离，且 $D_{ii}=0$。任选一个参考点 $a$，把距离表转成矩阵 $G$，其中 $G_{ij}=(D_{ia}+D_{ja}-D_{ij})/2$。Lean 定理 `squaredDistances_iff` 证明，能在 $d$ 维欧氏空间中实现这张距离表，当且仅当 $G$ 半正定且秩不超过 $d$。

必要性来自把参考点平移到原点，此时 $G$ 就是点向量的内积表。充分性调用等角直线档案的引理，从满足条件的 $G$ 得到点向量，再用内积算回原来的平方距离。[归档引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/annals_equiangular_lines_fixed_angle/Submission/Helpers.lean#L369)

以边长为 3、4、5 的三角形为例，选直角顶点作参考点，得到对角矩阵 $\operatorname{diag}(0,9,16)$，秩为 2。`triangle345_iff` 据此验证了平面可以实现这三段距离，直线不行。

两条定理均在固定版本的 Lean 和 Mathlib 下通过检查，公理输出都是 `propext`、`Classical.choice` 和 `Quot.sound`。[本地复核命令](README.md#check-locally) · [Lean 源码](EuclideanDistanceTable.lean)
