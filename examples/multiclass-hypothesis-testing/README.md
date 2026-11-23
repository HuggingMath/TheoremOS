# Accuracy bounds for multiclass hypothesis testing

[简体中文](README.zh-CN.md)

Suppose the true label is uniform among $k$ labels, and label $i$ produces a finite observation with law $P_i$. Write $M(y)=\sum_i P_i(y)/k$ for the mixture. For each output $y$, choose a label $d(y)$ with $P_{d(y)}(y)\ge M(y)$. Assume all the other labels have likelihood at most $M(y)$ at that output. This includes ties at the mixture value.

The chosen rule maximizes accuracy. Its gain above chance is the archive's reconstruction advantage, the average of $\operatorname{TV}(P_i,M)$. To see this, sum the positive deviations $\max(P_i(y)-M(y),0)$ over labels and observations. At each observation, only the chosen label can contribute. The archived `pmfTV_le_card_mul_reconAdvantage` lemma then gives, for every pair $i,j$,

$$
\Pr[d(Y)=I] \ge \frac{1}{k} + \frac{\operatorname{TV}(P_i,P_j)}{k}.
$$

[Archived lemma](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/Submission/Library/TheoremOS/Probability/TreeReconstruction.lean#L276) · [Archive verification record](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_three_state_tree_clauses/verification.json)

Lean checks two experiments with three equally likely labels. In both, the observation laws for labels $0$ and $1$ have total variation distance $1/2$.

| Experiment | Best prediction | Exact accuracy | Pairwise bound |
| --- | --- | ---: | ---: |
| The output matches the true label with probability $2/3$ and equals either alternative with probability $1/6$ each. | Predict the output label. | $2/3$ | $1/2$ |
| A binary output is heads with probabilities $3/4$, $1/4$, and $1/2$ under labels $0$, $1$, and $2$. | Predict label $0$ on heads and $1$ on tails. | $1/2$ | $1/2$ |

In the second experiment the mixture is a fair coin, so its total variation distances to the three laws are $1/4$, $1/4$, and $0$. Their average is $1/6$. Lean checks that both the archived bound $\operatorname{TV}(P_0,P_1)\le 3\cdot\operatorname{reconAdvantage}$ and the accuracy bound attain equality.

## Check locally

Run these commands from this directory with Git, curl, Elan and `sha256sum` available. The configuration pins Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

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

The five printed declarations use `propext`, `Classical.choice`, and `Quot.sound`. [Lean source](MulticlassHypothesisTesting.lean)
