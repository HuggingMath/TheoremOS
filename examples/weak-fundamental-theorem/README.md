# Recover a function from its weak derivative

[简体中文](README.zh-CN.md)

Suppose $f$ is locally integrable on $(a,b)$ and takes values in a real Banach space. Assume that every smooth scalar test function $\varphi$ with compact support in $(a,b)$ satisfies

$$
\int_{\mathbb R}\varphi'(t)f(t)\,dt=-\int_{\mathbb R}\varphi(t)g(t)\,dt,
$$

so $g$ is a weak derivative of $f$ there. When $g$ is continuous on $\mathbb R$, this example proves that $f(t)=C+\int_a^t g(s)\,ds$ almost everywhere on $(a,b)$. If $f$ is also continuous on the interval, its increment $f(y)-f(x)$ equals $\int_x^y g(t)\,dt$ at every pair of interior points. This recovers the displacement of a continuous curve whose velocity is specified by the test-function identity.

The Hopf–Rinow archive proves that a locally integrable function with zero weak derivative on an interval is constant almost everywhere. The example subtracts the ordinary primitive of $g$, uses integration by parts to show that the difference has zero weak derivative, and calls that archived lemma. [Archived lemma](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/hopf_rinow/Submission/Helpers.lean#L2018) · [Archive verification record](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/accepted/hopf_rinow/verification.json)

## Check locally

Run these commands from this directory with Git, curl, Elan and `sha256sum` available. The configuration pins Lean `4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

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

Lean checked the almost-everywhere result and the pointwise increment formula. Both use `propext`, `Classical.choice`, and `Quot.sound`. [Lean example](WeakFundamentalTheorem.lean)
