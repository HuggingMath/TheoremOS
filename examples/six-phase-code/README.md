# A distance test for a six-phase code

[简体中文](README.zh-CN.md)

Take a $6\times6$ matrix $H$ whose entries are sixth roots of unity. Assume $H$ and its entrywise square are both complex Hadamard matrices. Cubing gives a binary word for each row, with symbols $1$ and $-1$. Squaring gives a ternary word, with the three cube roots of unity as symbols.

For two distinct rows, group the coordinates by whether their binary words agree. In either group with any coordinates, the ternary words agree at exactly one third of the coordinates. A group of three coordinates therefore contains one ternary match. Each group has size divisible by three, so the binary Hamming distance is $0$, $3$, or $6$. A candidate pair that differs in two binary positions rules out the two Hadamard conditions holding together.

Two distinct projected binary words have distance at least $3$. A received word at distance at most $1$ from a projected word therefore determines that word uniquely. Several matrix rows can share a binary word.

The archived lemma `OAI.HadamardSix.rowRatio_cubeFiber_sum_zero` gives zero sum for the complex row ratios in each binary group. All ratios in a group have the same cube. Combined with the unit modulus of the ratios, this makes their squares and fourth powers sum to zero as well. Summing $1+r^2+r^4$ over a group counts three times the ternary matches, because the expression equals $3$ when $r^2=1$ and $0$ otherwise. [Archived lemma](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_hadamard_cube_fiber/Submission.lean#L28) · [Archive verification record](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_hadamard_cube_fiber/verification.json)

## Check locally

Run these commands from this directory with Git, curl, Elan and `sha256sum` available. The configuration pins Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

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

The ternary match count, binary distance restriction and one-error uniqueness statement all passed Lean. Each depends on `propext`, `Classical.choice`, and `Quot.sound`. [Lean example](SixPhaseCode.lean)
