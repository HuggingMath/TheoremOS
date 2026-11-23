# Budgeted matching after a triangle expansion

[简体中文](README.zh-CN.md)

Suppose a linear program chooses a point of the perfect matching polytope. Each edge has a price and a resource requirement, and the total resource use must fit a budget. The graph has a perfect matching and the vertex to be expanded has degree three. Replace that vertex with a triangle and attach the three original edges to different corners.

The archive identifies the original polytope with the face of the expanded polytope whose cut around the triangle has total weight one. The map preserves every original edge coordinate. The new Lean theorem `attainable_costs_eq` uses this correspondence to carry both the budget constraint and the objective through the expansion. With prices and resource use measured on the original edges, the two linear programs have exactly the same attainable costs, including when the budget makes both infeasible. Their variables are points of matching polytopes and can be convex combinations of matchings. [Archived triangle expansion theorem](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_triangle_face/Submission.lean#L1186)

## Check locally

Run these commands here with Git, curl, Elan and `sha256sum`. The configuration pins Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```bash
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_triangle_face/Submission.lean \
  -o ArchivedTriangleFace.lean
sha256sum -c - <<'EOF'
1f05b4d19928f89030bbe1ef6430f9b06bcca2273e082c8e339f77e44cdcf450  ArchivedTriangleFace.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build ArchivedTriangleFace
lake env lean WeightedTriangleMatching.lean
```

The last command prints the theorem's dependencies on `propext`, `Classical.choice` and `Quot.sound`. [Lean example](WeightedTriangleMatching.lean) · [Archive reuse terms](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/docs/PUBLIC-MATERIALS.md)
