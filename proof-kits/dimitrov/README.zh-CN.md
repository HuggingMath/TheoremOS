# Dimitrov 定理独立复核包（Proof Kit）

[English](./README.md) | [返回仓库首页](https://github.com/LikC1606/TheoremOS/blob/main/README.zh-CN.md) | [独立复核总指南](https://github.com/LikC1606/TheoremOS/blob/main/docs/VERIFY.zh-CN.md)

本复核包提供自包含的本地验证工作区，供数学家与形式化研究者在无需 TheoremOS 账号、无需 API Key、也不调用大模型的情况下，在本地 Linux 机器上用 Lean 4 内核与上游固定比较器独立检查 `Submission.dimitrov` 的形式化证明。

## 数学命题与固定环境

- **定理内容（`Submission.dimitrov`）**：在题面给定的非零代数整数且非单位根条件下，其 house（共轭元绝对值的最大值）满足由复嵌入辐角个数给出的显式下界。完整假设与公式定义见 [`Challenge.lean`](./Challenge.lean)，证明源码见 [`Submission.lean`](./Submission.lean) 与辅助引理 [`Submission/Helpers.lean`](./Submission/Helpers.lean)。
- **原样保留的上游与归档文件**：原题面（`Challenge.lean`）、桥接与测试文件（`Solution.lean`、`WorkspaceTest.lean`）、比较器配置（`config.json`、`holes.json`）、归档证明源码（`Submission.lean`、`Submission/Helpers.lean`）以及环境锁定文件（`lean-toolchain`、`lakefile.toml`、`lake-manifest.json`）均直接复制自上游基准或公开证明档案，字节未作修改。包内的 `Check.lean`、`verify.py` 与 `install-tools.sh` 是为本次复核包新增的验证脚本与辅助入口。
- **固定版本与来源记录**：
  - Lean 工具链：`leanprover/lean4:v4.35.0-rc3`
  - Mathlib 提交：`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`
  - Lean-Eval 提交：`38361be884302c7edce1908c4aef8296eb2cb27e`
  - 上游历史通过记录：[leanprover/lean-eval-submissions#2143 (comment)](https://github.com/leanprover/lean-eval-submissions/issues/2143#issuecomment-6215093969)
  - 复制文件的上游来源映射见 [`sources.json`](./sources.json)，全包所有文件（含新增脚本与文档）的 SHA256 清单见 [`SHA256SUMS`](./SHA256SUMS)。

## 获取复核包与校验完整性

您可以从克隆的公开仓库直接执行 `cd proof-kits/dimitrov`，或下载独立发行版压缩包：

- 压缩包：[theoremos-dimitrov-proof-kit-20261108.zip](https://github.com/LikC1606/TheoremOS/releases/download/v0.1.0-preview.1/theoremos-dimitrov-proof-kit-20261108.zip)
- 校验文件：[theoremos-dimitrov-proof-kit-20261108.zip.sha256](https://github.com/LikC1606/TheoremOS/releases/download/v0.1.0-preview.1/theoremos-dimitrov-proof-kit-20261108.zip.sha256)

将上述两个文件下载到同一目录后，依次校验 SHA256、解压并进入目录：

```bash
sha256sum -c theoremos-dimitrov-proof-kit-20261108.zip.sha256
unzip theoremos-dimitrov-proof-kit-20261108.zip
cd theoremos-dimitrov-proof-kit
```

## 系统要求

- **基础环境**：`git`、`python3`、`elan`（安装方式见 [Lean 官方安装指南](https://lean-lang.org/install/)）及网络连接。本包不含预编译的 Mathlib 缓存，首次运行需联网获取依赖与缓存。
- **完整比较器环境**：运行默认完整检查（含上游 comparator 与 `nanoda`）需使用 **Linux**（依赖 `landrun` 沙箱），并安装 **Go**、**Rust / Cargo** 与 **C 编译器**。脚本 `install-tools.sh` 会编译外部验证工具（`lean4export`、`comparator`、`nanoda_bin`、`landrun`）并安装到包外目录，其中两个 Lean 工具使用与本包相同的 Lean 版本，这不会安装 TheoremOS 运行时。

## 分步复核命令

在复核包根目录下按顺序执行（任何非零退出码均表示检查未通过）：

### 第 1 步：核对包内文件哈希

根据 `SHA256SUMS` 校验包内文件完整性（不启动 Lean）：

```bash
python3 verify.py --check-files
```

### 第 2 步：首次准备依赖并运行纯 Lean 检查

首次运行必须加上 `--prepare`，使脚本按原 `lake-manifest.json` 拉取固定依赖与 Mathlib 缓存（请勿手动运行 `lake update`，否则会改写归档的 manifest）。此命令会构建 `Submission` 与 `Solution`，并编译 `Check.lean` 打印 `Submission.dimitrov` 的公理列表供 `verify.py` 核对。若只需做纯 Lean 内核与公理检查，可在此步结束；注意 `--lean-only` 不会运行上游 comparator 和 `nanoda`：

```bash
python3 verify.py --prepare --lean-only
```

### 第 3 步：安装外部比较器工具并运行完整检查

以下三条命令依次将外部比较器工具编译到包外路径、加载生成的 `COMPARATOR_*` 环境变量，并运行默认完整检查（复用第 2 步构建结果，通过 `lake test` 对比冻结题面并强制运行 `nanoda`）：

```bash
bash install-tools.sh "$HOME/.cache/theoremos-proof-tools/dimitrov"
source "$HOME/.cache/theoremos-proof-tools/dimitrov/env.sh"
python3 verify.py
```

若缺少外部比较器工具，直接运行 `python3 verify.py` 会在完成 Lean 构建后调用比较器时以非零退出码报错，不会自动降级为 `--lean-only`。

## 判定标准与验证报告

- **公理与 `sorry` 检查**：仅允许标准公理 `propext`、`Quot.sound`、`Classical.choice`，拒绝 `sorryAx` 或自定义公理。上游题面模板 `Challenge.lean` 本身带有占位的 `sorry`；`Check.lean` 负责编译显式目标类型并输出 `#print axioms Submission.dimitrov`，由 `verify.py` 核对公理列表，随后 `lake test` 进一步对比冻结题面并调用 `nanoda`。
- **输出日志**：每次运行均在 `verification-output/` 下生成分步日志与 `report.json`。包内同时保留了历史归档记录 [`verification.json`](./verification.json) 与本次复核包重检报告 [`validation/report.json`](./validation/report.json)。
- **本次复核包实测结果**：2026-11-08 已实际通过 `Submission` / `Solution` 编译、目标类型与公理检查，以及原版 `lake test`。原比较器、Lean 默认内核与独立的 `nanoda` 内核均接受该证明；允许公理为 `Classical.choice`、`Quot.sound`、`propext`。

## 许可与署名

上游 Lean-Eval 工作区文件遵循 [`LICENSE.lean-eval`](./LICENSE.lean-eval)（Apache-2.0，见 [`UPSTREAM-README.md`](./UPSTREAM-README.md)），TheoremOS 验证脚本与包装材料遵循 [`LICENSE.TheoremOS`](./LICENSE.TheoremOS) 及原始档案署名。发布本复核包不将整个压缩包或 TheoremOS 运行时重授权为 Apache-2.0。
