# TheoremOS Access Guide / 访问说明

[English](#english) | [中文](#中文)

---

## English

### 1. Online Cloud Workbench (Research Preview)
- **Entry**: [https://app.theoremos.top/](https://app.theoremos.top/) (Website: [https://theoremos.top/en/](https://theoremos.top/en/))
- **How to Apply & Sign In**:
  1. Submit an [Early Access Request Issue](https://github.com/LikC1606/TheoremOS/issues/new?template=early-access.yml) or email **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** briefly describing your intended research use (links to target problems or drafts are optional).
  2. After review, follow the reply instructions to privately confirm your email address.
  3. Once your email is added to the whitelist, sign in at [https://app.theoremos.top/](https://app.theoremos.top/) using an email verification code (no local Lean or Docker setup required).
- **Cost & API Keys**: Platform access is free during the preview. Users provide their own model API keys (BYOK) and pay model providers directly. The configured endpoint must support the **Responses API**.
- **Supported Inputs**: Natural language problem statements, TeX/LaTeX, or existing Lean 4 files (including partial proofs with `sorry`).

### 2. Core Runtime, CLI & Research Collaboration
- **Scope of This Repository**: [`LikC1606/TheoremOS`](https://github.com/LikC1606/TheoremOS) hosts the public product documentation, website snapshot, and public proof archives (`v0.1.0-preview.1`).
- **Runtime & CLI Availability**: The core execution runtime, CLI tool, and replaceable strategy modules are not publicly open-sourced, and no public CLI installer or source download is provided here. Workbench whitelist access does not grant source code licensing.
- **Research Collaboration**: Researchers interested in CLI-based controlled experiments, strategy ablations, or component-level collaboration may contact **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** with a brief description of their research scenario. Requests are discussed case by case.

---

## 中文

### 1. 云端工作台（研究内测）
- **访问入口**：[https://app.theoremos.top/](https://app.theoremos.top/)（产品官网：[https://theoremos.top/](https://theoremos.top/)）
- **申请与登录步骤**：
  1. 通过 [GitHub 内测申请表单](https://github.com/LikC1606/TheoremOS/issues/new?template=early-access.yml) 或发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 简要说明您的研究用途（拟研究题目或草稿链接可选填）。
  2. 申请审核通过后，按回复指引私下确认需要开通的邮箱地址。
  3. 邮箱加入白名单后，即可在 [https://app.theoremos.top/](https://app.theoremos.top/) 通过邮箱验证码直接登录使用，无需在本地安装配置 Lean 或 Docker。
- **费用与模型密钥**：内测期间平台本身免费，采用用户自备 API Key（BYOK）模式，模型调用费用由用户向模型服务商支付。所接入的模型服务需支持 **Responses API**。
- **支持输入**：自然语言数学问题、TeX/LaTeX 题目，或已有的 Lean 4 题目及未完成证明。

### 2. 核心运行时、CLI 与研究合作
- **本仓库公开范围**：[`LikC1606/TheoremOS`](https://github.com/LikC1606/TheoremOS) 托管公开产品文档、官网快照与公开证明档案（`v0.1.0-preview.1`）。
- **运行时与 CLI 说明**：核心运行时源码、命令行工具（CLI）及可替换研究策略组件目前不公开；本仓库不提供 CLI 安装包或运行时源码下载，在线工作台内测资格亦不代表源码授权。
- **研究访问与合作联系**：如希望使用 CLI 开展受控实验、策略消融或组件级研究合作，请发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 简要说明研究用途与设想，我们将根据具体课题沟通合作方式。
