# 六相位码的距离判据

[English](README.md)

设 $H$ 是一个 $6\times6$ 矩阵，元素都是六次单位根，且 $H$ 和它的逐项平方矩阵均为复 Hadamard 矩阵。逐项取三次幂，每行得到一个符号为 $1$ 或 $-1$ 的二元码字。逐项平方，每行得到一个以三个三次单位根为符号的三元码字。

取两条不同的矩阵行，按对应二元符号是否相同，把坐标分成两组。每个非空组中，三元符号恰好在三分之一的坐标上相同。例如，一组有三个坐标，其中恰有一个三元符号匹配。两组的大小都是 $3$ 的倍数，所以二元汉明距离只能是 $0$、$3$ 或 $6$。如果候选矩阵有两行的二元投影相差两位，这两个 Hadamard 条件就无法同时成立。

两个不同的二元投影码字至少相差三位。因此，接收码字若与某个二元投影码字至多相差一位，就能唯一确定该二元码字。多个矩阵行可能对应同一个二元码字。

档案中的 `OAI.HadamardSix.rowRatio_cubeFiber_sum_zero` 证明每组内的复数行比值之和为零。结合组内比值有相同的三次幂，且模长都为 $1$，可得其平方与四次幂之和也分别为零。把 $1+r^2+r^4$ 在一组中求和，就得到三元符号匹配数的三倍，因为 $r^2=1$ 时该式为 $3$，其余情况为 $0$。[归档引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_hadamard_cube_fiber/Submission.lean#L28) · [归档检查记录](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_hadamard_cube_fiber/verification.json)

## 本地复核

安装 Git、curl、Elan 和 `sha256sum` 后，在本目录运行以下命令。配置固定了 Lean `4.34.1` 和 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。

```bash
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_hadamard_cube_fiber/Submission.lean \
  -o ArchivedHadamardCubeFiber.lean
sha256sum -c - <<'EOF'
d818e4c8217e53057b254f92285bb22930f2b47504ed68d7e8def9d2547fa3a1  ArchivedHadamardCubeFiber.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build ArchivedHadamardCubeFiber
lake env lean SixPhaseCode.lean
```

三元匹配计数、二元距离限制和单比特纠错唯一性均通过 Lean 检查，只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。[Lean 示例](SixPhaseCode.lean)
