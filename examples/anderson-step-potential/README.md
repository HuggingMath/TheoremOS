# The spectrum of a deterministic step potential

[简体中文](README.zh-CN.md)

The original planar Anderson problem uses an i.i.d. uniform potential. This example keeps the four nearest neighbours on the square lattice and sets the potential to $-h$ on the left half-plane and $h$ on the right.

The archived lemma `finite_box_approx_eigenvector` gives approximate eigenvectors for energies in $[-4+c,4+c]$ wherever there are arbitrarily large squares at constant potential $c$. Place a square of radius $N$ at $(-N-1,0)$ or $(N,0)$, then use `cps_mem_spectrum_of_approx` to obtain both spectral bands $[-4-h,4-h]$ and $[-4+h,4+h]$. For $0\le h\le 4$, the bands touch or overlap and the archived norm bound gives the full spectrum $[-4-h,4+h]$. [Archived finite-square lemma](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1206)

## Check locally

Run the following commands from this directory with Git, curl, Elan and `sha256sum` available. The configuration pins Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```bash
mkdir -p OAI/MathematicalPhysics/PlanarAnderson
curl -fLsS \
  https://raw.githubusercontent.com/HuggingMath/TheoremOS/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_planar_anderson_spectrum/Submission.lean \
  -o OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean
sha256sum -c - <<'EOF'
2fd7e2d1c71eff673ce58cd82f694526f9d6ed0a4ace42f800b159b26482cfc7  OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean
EOF
lake update --keep-toolchain
lake exe cache get
lake build OAI.MathematicalPhysics.PlanarAnderson.Spectrum
lake env lean AndersonStepPotential.lean
```

Lean checked both spectral statements locally. Both use `propext`, `Classical.choice`, and `Quot.sound`. A follow-up exercise is to move the boundary to $x_1=m$ and shift both square centres by $m$. [Lean example](AndersonStepPotential.lean)
