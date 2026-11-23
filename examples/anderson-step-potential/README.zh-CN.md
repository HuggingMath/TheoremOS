# 用 Anderson 档案里的引理计算确定性阶跃势的谱

[English](README.md)

Anderson 档案的原题研究二维格点上的独立均匀随机势。这次仍用四个最近邻的邻接算子，势函数换成确定性的阶跃函数。给定 $h\geq 0$，第一坐标 $x_1<0$ 时取 $-h$，$x_1\geq 0$ 时取 $h$。我们想知道两侧的常数区域各自给谱贡献了什么。[Anderson 原题与证明](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/docs/CASE-STUDY.zh-CN.md)

| 区域 | 势 | 可证落在谱里的区间 |
| --- | --- | --- |
| 左半平面 | $-h$ | $[-4-h,4-h]$ |
| 右半平面 | $h$ | $[-4+h,4+h]$ |

当 $0\leq h\leq 4$，两个区间相交或相接。结合档案对自伴算子的范数上界，整个谱恰好是 $[-4-h,4+h]$。

## 怎样复用原证明

在常数势为 $c$ 的足够大方块内，档案引理 `finite_box_approx_eigenvector` 为 $[-4+c,4+c]$ 中任意能量构造近似特征向量。把半径为 $N$ 的方块分别放在 $(-N-1,0)$ 和 $(N,0)$，就能让它完全落在一侧。示例借助 `cps_mem_spectrum_of_approx` 把任意精度的近似变成谱成员结论。两处都直接调用原文件中的引理。[有限方块引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_planar_anderson_spectrum/Submission.lean#L1206) · [近似特征向量引理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_planar_anderson_spectrum/Submission.lean#L885)

可以继续试一个变式。把分界线挪到 $x_1=m$，其中 $m$ 是任意整数。在 [Lean 示例](AndersonStepPotential.lean)中改动势函数和两个方块中心的横坐标，原来的有限方块引理仍可直接调用。

## 本地检查

将 `AndersonStepPotential.lean`、`lakefile.toml` 和 `lean-toolchain` 放在同一目录。以下命令从该目录运行，需要 Git、curl、Elan、`sha256sum` 和网络连接。配置锁定 Lean `4.34.1` 和 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。上游文件按档案中的许可说明使用。[档案许可说明](https://github.com/HuggingMath/TheoremOS/blob/main/docs/PUBLIC-MATERIALS.md)

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

本地检查覆盖两条定理。`stepPotential_spectrum_bands` 给出区间包含，`stepPotential_spectrum` 在两个区间相交或相接时给出全谱等式。两条定理的公理输出均为 `propext`、`Classical.choice`、`Quot.sound`。
