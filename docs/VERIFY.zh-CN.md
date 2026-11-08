# 复核一份公开证明

[English](VERIFY.md) · [TheoremOS](../README.zh-CN.md)

公开证明包可以使用 Lean 和原基准工具检查，无需 TheoremOS 账号、私有运行时或模型 API Key。

## 快速检查：官网回放中的小例子

先安装 Git、Python 3 和 [Elan / Lean](https://lean-lang.org/install/)。这个[简短示例](../examples/lean-check/Submission.lean)仅使用 Lean 标准库，证明[官网预设回放](https://theoremos.top/#demo)中的两个陈述：`Tutorial.add_zero` 和 `Tutorial.zero_add`。

```bash
git clone https://github.com/LikC1606/TheoremOS.git
cd TheoremOS
elan toolchain install leanprover/lean4:v4.33.0
lean +leanprover/lean4:v4.33.0 examples/lean-check/Submission.lean
```

命令应成功退出，并打印两条定理均不依赖任何公理。这个例子用于体验检查流程，不需要 Mathlib 或模型调用；后文的研究证明记录各有对应的陈述和环境。

## Dimitrov：复核一份归档证明

下面以 [Dimitrov 下界证明](../accepted/dimitrov/)为例。它已有 [Lean-Eval 官方通过记录](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969)，归档环境固定为：

| 项目 | 版本 |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22` |
| 原 Lean-Eval 工作区 | `38361be884302c7edce1908c4aef8296eb2cb27e` |
| 提交的定理 | `Submission.dimitrov` |

**完整下载包：**[Dimitrov 证明复核包](../proof-kits/dimitrov/README.zh-CN.md)已包含固定的基准工作区、归档证明、依赖版本、检查脚本和报告，可按包内说明直接复核。

### 1. 核对归档文件

在上一步克隆的公开仓库根目录执行：

```bash
git rev-parse HEAD

python3 - <<'PY'
from pathlib import Path
import hashlib
import json

records = json.loads(Path('accepted/accepted.json').read_text())
record = next(item for item in records if item['problem_id'] == 'dimitrov')
package = Path('accepted') / record['directory']
for relative_path, expected in record['source_sha256'].items():
    actual = hashlib.sha256((package / relative_path).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'Hash mismatch: {relative_path}')
    print(f'PASS {relative_path}')
PY
```

请将打印出的仓库提交版本与检查结果一起保存。哈希核对用于确认归档证明及环境文件的身份，这一步尚未运行 Lean。

### 2. 恢复原基准工作区

归档目录保存提交的证明文件，并非完整基准工作区。需要从记录的 Lean-Eval 版本取得固定题面、连接提交定理的模块和检查程序：

```bash
cd ..
git clone https://github.com/leanprover/lean-eval.git
git -C lean-eval checkout 38361be884302c7edce1908c4aef8296eb2cb27e

cp -R lean-eval/generated/dimitrov verify-dimitrov
cp TheoremOS/accepted/dimitrov/Submission.lean verify-dimitrov/Submission.lean
cp -R TheoremOS/accepted/dimitrov/Submission/. verify-dimitrov/Submission/
cp TheoremOS/accepted/dimitrov/lake-manifest.json verify-dimitrov/lake-manifest.json
```

保留该固定工作区中的 `Challenge.lean`、`Solution.lean`、`WorkspaceTest.lean`、`config.json`、`lakefile.toml` 和 `lean-toolchain`。归档的 `lakefile.toml` 与 `lean-toolchain` 和它逐字节一致；复制的 manifest 用于固定归档中的依赖版本。

### 3. 编译提交的证明

首次准备会下载固定版本的 Lean 工具链、Mathlib 依赖和 Mathlib 编译缓存；已有兼容缓存时可以复用。

```bash
cd verify-dimitrov
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake exe cache get

lake env lean --version
git -C .lake/packages/mathlib rev-parse HEAD
lake build Submission
```

Lean 应报告 `4.35.0-rc3`，Mathlib 应处于上表记录的版本。`lake build Submission` 成功表示提交的定理及辅助证明通过了 Lean 编译检查。

### 4. 运行原比较器

要对照固定基准陈述检查证明，请按[同一 Lean-Eval 版本的比较器安装说明](https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/README.md#5-run-comparator-locally)准备工具。它固定了以下源码版本：

| 工具 | 固定提交 |
| --- | --- |
| `landrun` | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |
| `lean4export` | `076e8e57707e813375e8f9da8bf989799ace9680` |
| `comparator` | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| `nanoda_bin` | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

将这些工具安装在 `verify-dimitrov` 之外并加入 `PATH`，按上游说明使用与工作区完全相同的 Lean 工具链编译 Lean 工具。随后在 `verify-dimitrov` 中执行：

```bash
lake test
```

这会运行原比较器及其独立内核检查。本地运行通过意味着提交定理与固定的形式化基准陈述通过了检查；它与上文链接的历史官方托管结果分别记录，也不代表形式化陈述已经涵盖所有非形式化理解。

## 其他公开记录

检查其他 Lean-Eval 证明时，应使用各自的源码清单和基准版本，不能假定都使用本例的环境。[accepted](../accepted/accepted.json) 与 [submitted](../submitted/submitted.json) 索引保留了来源记录和官方结果链接。

[OpenAI Math 记录](../data/proofs/)公开了题面、证明源码、检查报告和研究过程。其中记录的本地 Lean 与原比较器检查，和 OpenAI 官方托管评测分别记录；目前尚未确认 OpenAI 的官方评测结果。请使用每条记录对应的题面和环境，不要将这些文件直接套入本例的 Dimitrov 工作区。
