# 三角展开后带预算的匹配优化

[English](README.md)

考虑一个在完美匹配多面体上求解的线性规划。每条边有价格和资源消耗，总消耗受预算限制。图存在完美匹配，把一个度数为 3 的顶点换成三角形，原来的三条边分别接到三个角上。

档案里的定理给出一个对应。原匹配多面体对应展开图中三角形割的总权重等于 1 的面，且原有边的坐标完全相同。新增的 Lean 定理 `attainable_costs_eq` 用这个对应同时转移预算约束和目标函数。只在原有边上计费、计资源消耗时，两个线性规划能达到的成本值完全相同。这里的变量可以是多个完美匹配的凸组合。 [档案原定理](https://github.com/HuggingMath/TheoremOS/blob/84e40d87325052a6489f9e9225b666c622f2c405/data/proofs/openai_triangle_face/Submission.lean#L1186)

示例用 Lean `4.34.1` 和固定版本的 Mathlib 复核。最后一条命令会打印定理用到的公理。 [本地复核命令](README.md#check-locally) · [Lean 示例](WeightedTriangleMatching.lean)
