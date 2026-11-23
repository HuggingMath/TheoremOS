# 从弱导数恢复函数

[English](README.md)

设 $f$ 在 $(a,b)$ 上局部可积，取值于实 Banach 空间。对每个支撑紧含于 $(a,b)$ 的光滑标量测试函数 $\varphi$，假设

$$
\int_{\mathbb R}\varphi'(t)f(t)\,dt=-\int_{\mathbb R}\varphi(t)g(t)\,dt.
$$

于是 $g$ 是 $f$ 在该区间上的弱导数。若 $g$ 在实轴上连续，本例证明 $f(t)=C+\int_a^t g(s)\,ds$ 在 $(a,b)$ 上几乎处处成立。若 $f$ 在区间上也连续，则任意两个内点都满足 $f(y)-f(x)=\int_x^y g(t)\,dt$。一条连续曲线的速度由测试函数恒等式给出时，可以用这个结论求它的位移。

Hopf–Rinow 档案证明了一条引理，说明区间上弱导数为零的局部可积函数几乎处处为常数。本例从 $f$ 减去 $g$ 的积分原函数，通过分部积分证明差的弱导数为零，再调用这条归档引理。[归档引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/hopf_rinow/Submission/Helpers.lean#L2018) · [归档检查记录](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/hopf_rinow/verification.json)

## 本地复核

安装 Git、curl、Elan 和 `sha256sum` 后，在本目录运行以下命令。配置固定了 Lean `4.35.0-rc3` 和 Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`。

```bash
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/accepted/hopf_rinow/Submission/Helpers.lean \
  -o ArchivedHopfRinowHelpers.lean
sha256sum -c - <<'EOF'
f62e16b14fff319f20788b03d94cf9de1262dcfa0cc6462b539faa5435573c40  ArchivedHopfRinowHelpers.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build ArchivedHopfRinowHelpers
lake env lean WeakFundamentalTheorem.lean
```

几乎处处成立的原函数公式与连续情形的逐点增量公式均通过 Lean 检查，只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。[Lean 示例](WeakFundamentalTheorem.lean)
