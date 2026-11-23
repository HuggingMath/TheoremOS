# Can these distances come from points in Euclidean space?

[简体中文](README.zh-CN.md)

Suppose $D_{ij}$ is a proposed table of squared distances, with $D_{ii}=0$. To check whether the distances can be realized in $\mathbb R^d$, choose an anchor $a$ and form the matrix

$$
G_{ij}=\frac{D_{ia}+D_{ja}-D_{ij}}{2}.
$$

The Lean theorem `squaredDistances_iff` proves that points with exactly these distances exist if and only if $G$ is positive semidefinite and has rank at most $d$. Translating the anchor to the origin gives the forward direction. For the reverse direction, the proof calls `positive_semidefinite_gram_realization` from the equiangular lines archive to obtain vectors with Gram matrix $G$. Their inner products recover the entries of $D$. [Archived Gram realization](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/annals_equiangular_lines_fixed_angle/Submission/Helpers.lean#L369)

For a 3–4–5 triangle, the squared distances are 9, 16 and 25. Anchoring at the right angle gives $G=\operatorname{diag}(0,9,16)$. Its rank is two, so the distances can be realized in the plane and require at least two dimensions. Lean checks this example as `triangle345_iff`.

## Check locally

Run these commands from this directory with Git, curl, Elan and `sha256sum`. The configuration pins Lean `4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

```bash
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/accepted/annals_equiangular_lines_fixed_angle/Submission/Helpers.lean \
  -o ArchivedEquiangularHelpers.lean
sha256sum -c - <<'EOF'
2b0ee3d08d6293710ee2348a00f8bd72e702332e7e05af0af61a434c6476e57f  ArchivedEquiangularHelpers.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build ArchivedEquiangularHelpers
lake env lean EuclideanDistanceTable.lean
```

Both theorems passed on Linux and depend on `propext`, `Classical.choice` and `Quot.sound`. [Lean source](EuclideanDistanceTable.lean) · [Archive reuse terms](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/docs/PUBLIC-MATERIALS.md)
