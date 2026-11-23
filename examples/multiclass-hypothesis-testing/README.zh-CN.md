# 多类假设检验的准确率下界

[English](README.md)

有 $k$ 个等概率的类别。真实类别为 $i$ 时，有限观察结果服从分布 $P_i$。记 $M(y)=\sum_i P_i(y)/k$ 为混合分布。对每个观察结果 $y$，选一个似然 $P_{d(y)}(y)\ge M(y)$ 的类别 $d(y)$，并假设其余类别在该观察点的似然都不超过 $M(y)$。允许多个类别的似然同时等于混合值。

这条规则达到最优准确率。它比随机猜测多出的准确率等于档案中的重构优势，即各类别分布与混合分布之间的平均总变差。计算时，把正偏差 $\max(P_i(y)-M(y),0)$ 在类别和观察结果上求和。每个观察点上，只有选中的类别可能贡献正偏差。再用档案引理 `pmfTV_le_card_mul_reconAdvantage`，即可对任意两个类别 $i,j$ 得到

$$
\Pr[d(Y)=I] \ge \frac{1}{k} + \frac{\operatorname{TV}(P_i,P_j)}{k}.
$$

[归档引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/Submission/Library/TheoremOS/Probability/TreeReconstruction.lean#L276) · [归档检查记录](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/verification.json)

Lean 还检验了两个三类等先验的实验。两者中，类别 $0$ 和类别 $1$ 的观察分布之间的总变差都是 $1/2$。

| 实验 | 最优预测 | 准确率 | 成对总变差给出的下界 |
| --- | --- | ---: | ---: |
| 以 $2/3$ 的概率观察到真实类别，另外两个类别各以 $1/6$ 的概率出现。 | 预测观察到的类别。 | $2/3$ | $1/2$ |
| 类别 $0$、$1$、$2$ 分别以 $3/4$、$1/4$、$1/2$ 的概率观察到正面。 | 正面预测类别 $0$，反面预测类别 $1$。 | $1/2$ | $1/2$ |

第二个实验的混合分布是一枚公平硬币。它与三个类别分布之间的总变差分别为 $1/4$、$1/4$、$0$，平均为 $1/6$。Lean 验证了归档不等式 $\operatorname{TV}(P_0,P_1)\le 3\cdot\operatorname{reconAdvantage}$ 与准确率下界在这里同时取等。

## 本地复核

安装 Git、curl、Elan 和 `sha256sum` 后，在本目录运行以下命令。配置固定了 Lean `4.34.1` 和 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。

```bash
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/Submission/Library/TheoremOS/Probability/TreeReconstruction.lean \
  -o ArchivedTreeReconstruction.lean
sha256sum -c - <<'EOF'
cf91591ad7ab77463ba4c64dee04529a87e730716380bc87a569359d2485f54e  ArchivedTreeReconstruction.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build ArchivedTreeReconstruction
lake env lean MulticlassHypothesisTesting.lean
```

输出的五条声明均只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。[Lean 源码](MulticlassHypothesisTesting.lean)
