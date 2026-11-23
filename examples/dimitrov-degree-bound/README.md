# 从 Dimitrov 下界到单位根判定

[English](#from-dimitrovs-bound-to-a-root-of-unity-test)

设 $K$ 是次数为 $d$ 的数域，$\alpha\ne 0$ 是其中的代数整数。如果每个复嵌入 $\sigma$ 下的 $|\sigma(\alpha)|$ 都严格小于 $2^{1/(4d)}$，就存在正整数 $n$ 使 $\alpha^n=1$。例如在二次数域里，若所有共轭的模都至多为 $21/20$，便可应用这个条件，因为 $(21/20)^8<2$。

原定理的下界使用共轭辐角的不同取值数。这个数至多是嵌入数 $d$，所以用 $d$ 替换它仍有一个下界。然后把最大共轭模与该下界比较，即得到单位根判定。[归档定理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/proof-kits/dimitrov/Submission.lean#L9) · [Lean-Eval 原题通过记录](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969)

## From Dimitrov’s bound to a root of unity test

Let $\alpha$ be a nonzero algebraic integer in a number field of degree $d$. If every complex conjugate has modulus strictly less than $2^{1/(4d)}$, then $\alpha^n=1$ for some positive integer $n$. For example, in degree two it suffices to bound every modulus by $21/20$, since $(21/20)^8<2$.

Dimitrov's bound uses the number of distinct arguments of the conjugates. That count is at most the number of embeddings, $d$. Replacing it by $d$ weakens the bound and gives a test that only needs the field degree and bounds on the moduli. [Archived theorem](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/proof-kits/dimitrov/Submission.lean#L9)

## 本地检查 / Check locally

解压原复核包，将 `DimitrovDegreeBound.lean` 放到包目录，在该目录运行下列两条命令。复核包固定了 Lean `4.35.0-rc3` 和 Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`。[中文复核包说明](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/proof-kits/dimitrov/README.zh-CN.md) · [Lean 示例](DimitrovDegreeBound.lean)

Unpack the pinned proof kit, put `DimitrovDegreeBound.lean` in its root, and run these commands there. [English proof kit instructions](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/proof-kits/dimitrov/README.md)

```sh
python3 verify.py --prepare --lean-only
lake env lean DimitrovDegreeBound.lean
```

两条新定理均已在复核包的固定环境中通过 Lean 检查，所用公理为 `propext`、`Classical.choice` 和 `Quot.sound`。
