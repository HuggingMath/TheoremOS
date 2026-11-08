# 公开证明档案与历史运行观察

[English](./EVALUATION.md) | [返回首页](../README.zh-CN.md) | [能力与范围](./CAPABILITIES.zh-CN.md) | [访问申请](./ACCESS.md) | [快速上手](./GETTING-STARTED.zh-CN.md) | [案例研究](./CASE-STUDY.zh-CN.md) | [独立复核指南](./VERIFY.zh-CN.md)

本页整理了 TheoremOS 公开目录中的证明档案与历史运行记录（整理日期：`2026-11-08`，公开档案快照时间：`2026-11-07T16:32:08.577Z`）。读者可通过本页了解哪些形式化目标已通过 Lean 检查、公开验证报告如何对应到具体运行，以及这些历史记录的统计边界。

本页是对已归档公开成果与历史运行记录的整理，不是在预先固定的题集分母和统一预算协议下运行的基准评测（Benchmark）。

## 公开数据概览与下载

读者可直接下载仓库中的结构化数据并使用脚本复算：

- 数据文件：[snapshot.json](../data/evaluation/snapshot.json)、[records.csv](../data/evaluation/records.csv)、[runs.csv](../data/evaluation/runs.csv)、[selected-run-observations.json](../data/evaluation/selected-run-observations.json)
- 复算脚本：[snapshot-evaluation.py](../scripts/snapshot-evaluation.py)

| 统计项 | 数量 | 来源与说明 |
| :--- | :--- | :--- |
| 公开目录总记录 | 27 | 包含 26 条已验证证明档案与 1 条进行中的研究快照。 |
| Lean-Eval 官方通过记录 | 10 | 6 条取自 `accepted/accepted.json`；4 条由 `submitted/official-results.json` 覆盖 `submitted/submitted.json` 的历史状态并通过 manifest 哈希校验。 |
| OpenAI Math 来源形式化档案 | 16 | 共包含 23 个形式化目标，已通过本项目的 Lean 编译与原题比较器检查（未经 OpenAI 官方评测确认）。 |
| 进行中的 Szemerédi 研究快照 | 1 | 公开目录状态为 `in_progress_not_officially_accepted`。 |
| OpenAI Math 档案去重运行数（`runId`） | 45 | 来自 16 个档案的 `process.json`：`evaluated_passed`（19）、`limit_reached`（17）、`prepared`（4）、`runtime_error`（3）、`incomplete`（1）、`evaluated_failed`（1）；其中 38 次运行记有起止时间戳。 |

**关于计数与验证绑定的说明**：

- 公开目录是在研究取得成果后筛选归档的，因此 `26/27` 和 16 个公开题目下的 `19/45` 都不能用来计算证明成功率。部分档案为辅助引理（`support`）、条件性命题或包含多个目标，单个档案通过验证不一定代表完整解决了原非形式化问题。
- 每个 OpenAI Math 档案的选中运行（Selected Run）由公开 `verification.json.runId` 指定，并通过 `runId`、solution commit 与证明文件 SHA256 对应到保存的原始运行结果。

## 16 个 OpenAI Math 档案的选中运行主表

下表列出 16 个 OpenAI Math 档案中由 `verification.json.runId` 绑定的那次运行的参数与耗时：

| 档案 / 验证报告 | 历史模型标签 | 本次运行时长（秒） | 轮数 | Agent 数 |
| --- | --- | --- | --- | --- |
| [Koebe 映射的锐端点发散](../data/proofs/openai_brennan_sharp/verification.json) | TheoremOS · deepseek-flash | 2,278.193 | 48 | 4 |
| [归一化 Cartier 坐标回缩的紧致性](../data/proofs/openai_cartier_chart_compactness_support/verification.json) | TheoremOS · deepseek-flash | 1,144.551 | 6 | 4 |
| [有限同余格的彩色图判据](../data/proofs/openai_finite_congruence_graph/verification.json) | TheoremOS · deepseek-flash | 1,721.562 | 26 | 4 |
| [六阶 Hadamard 行比值的立方纤维消去](../data/proofs/openai_hadamard_cube_fiber/verification.json) | TheoremOS · deepseek-flash | 966.516 | 4 | 4 |
| [数值域几何与有限压缩辅助结果](../data/proofs/openai_hilbert_crouzeix/verification.json) | TheoremOS · deepseek-flash | 15,498.495 | 55 | 4 |
| [蜂窝格自由能极限的存在性](../data/proofs/openai_honeycomb_free_energy/verification.json) | TheoremOS · deepseek-flash | 3,985.297 | 31 | 4 |
| [Ising 感知器变分值的有限性](../data/proofs/openai_ising_finiteness/verification.json) | TheoremOS · deepseek-flash | 9,367.002 | 54 | 4 |
| [平面 Anderson 算子的几乎必然谱](../data/proofs/openai_planar_anderson_spectrum/verification.json) | TheoremOS · deepseek-flash | 14,032.263 | 107 | 4 |
| [欧氏平面的七色着色](../data/proofs/openai_plane_coloring/verification.json) | TheoremOS · deepseek-flash | 8,166.647 | 13 | 4 |
| [Snaky 的 35 步证书核验](../data/proofs/openai_snaky_certificate/verification.json) | TheoremOS · deepseek-flash | 13,754.834 | 27 | 4 |
| [Snaky 的 35 步获胜策略](../data/proofs/openai_snaky_conditional/verification.json) | TheoremOS · deepseek-flash | 33,443.284 | 7 | 4 |
| [三维完备局部候选环](../data/proofs/openai_surface_cone_candidate_support/verification.json) | TheoremOS · deepseek-flash | 2,073.492 | 10 | 4 |
| [正则树与泊松树上的超临界重构](../data/proofs/openai_three_state_supercritical/verification.json) | TheoremOS · deepseek-flash | 13,529.770 | 66 | 4 |
| [欧拉函数伴随定理的零值情形](../data/proofs/openai_totient_companion_zero/verification.json) | TheoremOS · deepseek-flash | 3,277.751 | 11 | 4 |
| [三角展开下匹配多面体的面对应](../data/proofs/openai_triangle_face/verification.json) | TheoremOS · deepseek-flash | 2,843.712 | 18 | 4 |
| [Truffet 优化程序的有限反例](../data/proofs/openai_truffet_counterexample/verification.json) | TheoremOS · deepseek-flash | 839.532 | 1 | 4 |

表中时长仅计算该次选中运行的 `finishedAt - startedAt`，不包含此前的失败尝试、继承自早期草稿的证明片段或外部人工分析时间，因此不是从零解出该题的总耗时。模型标签直接引用自公开 catalog 字段，并非对底层每次 API 调用逐一核对后的清单。这 16 次选中运行均使用 4 个 Agent。

## 选中运行的资源报告与历史启动预算

下表列出上述 16 次选中运行在原始结果中记录的 Token 数（`inputTokens` / `outputTokens` / `totalTokens`）、计量完整性标记（`usageComplete`），以及对应启动参数中的历史预算设置：

| 档案 | 已报告输入 Token | 已报告输出 Token | 已报告总 Token | 计量完整 | 时间上限（秒） |
| --- | --- | --- | --- | --- | --- |
| [Koebe 映射的锐端点发散](../data/proofs/openai_brennan_sharp/verification.json) | 73,876,775 | 3,124,376 | 77,001,151 | `false` | 3,597 |
| [归一化 Cartier 坐标回缩的紧致性](../data/proofs/openai_cartier_chart_compactness_support/verification.json) | 1,358,267 | 53,475 | 1,411,742 | `false` | 14,400 |
| [有限同余格的彩色图判据](../data/proofs/openai_finite_congruence_graph/verification.json) | 32,037,290 | 1,202,033 | 33,239,323 | `false` | 14,400 |
| [六阶 Hadamard 行比值的立方纤维消去](../data/proofs/openai_hadamard_cube_fiber/verification.json) | 1,704,708 | 89,908 | 1,794,616 | `false` | 不限 |
| [数值域几何与有限压缩辅助结果](../data/proofs/openai_hilbert_crouzeix/verification.json) | 81,047,140 | 3,166,088 | 84,213,228 | `false` | 不限 |
| [蜂窝格自由能极限的存在性](../data/proofs/openai_honeycomb_free_energy/verification.json) | 19,521,397 | 626,066 | 20,147,463 | `false` | 14,400 |
| [Ising 感知器变分值的有限性](../data/proofs/openai_ising_finiteness/verification.json) | 37,973,642 | 2,165,385 | 40,139,027 | `false` | 14,399 |
| [平面 Anderson 算子的几乎必然谱](../data/proofs/openai_planar_anderson_spectrum/verification.json) | 183,936,328 | 7,824,864 | 191,761,192 | `false` | 14,398 |
| [欧氏平面的七色着色](../data/proofs/openai_plane_coloring/verification.json) | 12,979,862 | 459,185 | 13,439,047 | `false` | 14,400 |
| [Snaky 的 35 步证书核验](../data/proofs/openai_snaky_certificate/verification.json) | 104,951,968 | 3,514,812 | 108,466,780 | `false` | 不限 |
| [Snaky 的 35 步获胜策略](../data/proofs/openai_snaky_conditional/verification.json) | 8,369,984 | 129,494 | 8,499,478 | `false` | 不限 |
| [三维完备局部候选环](../data/proofs/openai_surface_cone_candidate_support/verification.json) | 9,083,734 | 338,821 | 9,422,555 | `false` | 不限 |
| [正则树与泊松树上的超临界重构](../data/proofs/openai_three_state_supercritical/verification.json) | 132,487,580 | 5,321,780 | 137,809,360 | `false` | 不限 |
| [欧拉函数伴随定理的零值情形](../data/proofs/openai_totient_companion_zero/verification.json) | 4,627,667 | 170,832 | 4,798,499 | `false` | 14,400 |
| [三角展开下匹配多面体的面对应](../data/proofs/openai_triangle_face/verification.json) | 14,324,003 | 408,272 | 14,732,275 | `false` | 不限 |
| [Truffet 优化程序的有限反例](../data/proofs/openai_truffet_counterexample/verification.json) | 1,831,984 | 94,339 | 1,926,323 | `true` | 不限 |

**阅读此表需注意三点**：

- **运行时已报告 Token 不完整**：16 次选中运行中有 15 次的 `usageComplete` 为 `false`，仅 `TruffetCounterexample` 为 `true`（且只代表该次选中运行记录完整，不含早期探索）。表中数字仅反映运行时已报告用量，不能相加估算总花费，也不宜用于跨系统成本对比。
- **预算中的 `0` 表示不设上限**：在历史启动参数中，16 次运行的 Token、轮次、单轮时间与比较器时间上限均为 `0`，在运行时配置中代表“不限（unlimited）”，而非消耗为零。总时间上限也不统一（部分为不限，部分为 `3597`、`14398`、`14399` 或 `14400` 秒），反映不同阶段的历史探索，不代表当前网页工作台的默认预算。
- **原始结果范围**：原始运行结果与启动记录保存在私有环境中；[selected-run-observations.json](../data/evaluation/selected-run-observations.json) 公开了摘要统计字段及对应私有文件的 SHA256 哈希。外部读者可核对证明文件绑定并复算公开表格，但无法仅凭公开仓库核查模型服务商的逐笔请求账单。

## 为什么部分系统级指标记为 `null`

在 [snapshot.json](../data/evaluation/snapshot.json) 中，以下指标记为 `null`（表示在当前历史数据下无法给出有效统计，不等于 `0`）：

- **整体基准成功率**：`null`（无预先锁定的固定题集分母）。
- **从零求解端到端总时长**：`null`（历史档案包含多轮迭代与草稿继承）。
- **单题全周期 Token 与总费用**：`null`（无统一实验协议，且 15/16 次选中运行 `usageComplete=false`）。

## 本地核对与复算命令

在仓库根目录下运行以下只读命令，可核对 `catalog`、`accepted/accepted.json`、`submitted/official-results.json`、`process.json`、`verification.json`、证明文件 SHA256 与公开数据表是否一致；若去掉 `--check` 则会重新生成快照文件：

```bash
python3 scripts/snapshot-evaluation.py --check
python3 scripts/snapshot-evaluation.py
```
