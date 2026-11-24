# TheoremOS Access Guide / 访问说明

[English](#english) | [中文](#中文)

---

## English

### 1. Online Cloud Workbench (Research Preview)
- **Entry**: [https://app.theoremos.top/](https://app.theoremos.top/) (Website: [https://theoremos.top/en/](https://theoremos.top/en/))
- **How to Apply & Sign In**:
  1. Submit an [Early Access Request Issue](https://github.com/HuggingMath/TheoremOS/issues/new?template=early-access.yml) or email **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** briefly describing your intended research use (links to target problems or drafts are optional).
  2. After review, follow the reply instructions to privately confirm your email address.
  3. Once your email is added to the whitelist, sign in at [https://app.theoremos.top/](https://app.theoremos.top/) using an email verification code (no local Lean or Docker setup required).
- **Cost & API Keys**: Platform access is free during the preview. Users provide their own model API keys (BYOK) and pay model providers directly. The configured endpoint must support the **Responses API**.
- **Supported Inputs**: Natural language problem statements, TeX/LaTeX, or existing Lean 4 files (including partial proofs with `sorry`).

**Next**: Follow the [illustrated first-use tutorial](GETTING-STARTED.md), check [capabilities and availability](CAPABILITIES.md), or read the [planar Anderson spectrum case study](CASE-STUDY.md).

### 2. Core Runtime, CLI & Research Collaboration
- **Scope of This Repository**: [`HuggingMath/TheoremOS`](https://github.com/HuggingMath/TheoremOS) hosts the public product documentation, website snapshot, and public proof archives (`v0.1.0-preview.1`).
- **Workbench & CLI Source**: The workbench, CLI tool, and replaceable strategy modules are published separately at [`HuggingMath/theorem-os`](https://github.com/HuggingMath/theorem-os) under `AGPL-3.0-only`.
- **Research Collaboration**: Researchers interested in joint multi-file Lean projects, controlled experiments, or WestlakeNLP research collaboration may contact **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** with a brief description of their research scenario. Requests are discussed case by case.

---

## 中文

### 1. 云端工作台（研究内测）
- **访问入口**：[https://app.theoremos.top/](https://app.theoremos.top/)（产品官网：[https://theoremos.top/](https://theoremos.top/)）
- **申请与登录步骤**：
  1. 通过 [GitHub 内测申请表单](https://github.com/HuggingMath/TheoremOS/issues/new?template=early-access.yml) 或发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 简要说明您的研究用途（拟研究题目或草稿链接可选填）。
  2. 申请审核通过后，按回复指引私下确认需要开通的邮箱地址。
  3. 邮箱加入白名单后，即可在 [https://app.theoremos.top/](https://app.theoremos.top/) 通过邮箱验证码直接登录使用，无需在本地安装配置 Lean 或 Docker。
- **费用与模型密钥**：内测期间平台本身免费，采用用户自备 API Key（BYOK）模式，模型调用费用由用户向模型服务商支付。所接入的模型服务需支持 **Responses API**。
- **支持输入**：自然语言数学问题、TeX/LaTeX 题目，或已有的 Lean 4 题目及未完成证明。

**接下来**：查看[首次使用图文教程](GETTING-STARTED.zh-CN.md)、[能力与开放范围](CAPABILITIES.zh-CN.md)，或阅读[平面 Anderson 算子谱研究案例](CASE-STUDY.zh-CN.md)。

### 2. 核心运行时、CLI 与研究合作
- **本仓库公开范围**：[`HuggingMath/TheoremOS`](https://github.com/HuggingMath/TheoremOS) 托管公开产品文档、官网快照与公开证明档案（`v0.1.0-preview.1`）。
- **工作台与 CLI 源码**：工作台、CLI 工具与可替换研究策略组件源码托管于 [`HuggingMath/theorem-os`](https://github.com/HuggingMath/theorem-os)（采用 `AGPL-3.0-only`）。
- **研究访问与合作联系**：如希望围绕多文件 Lean 工程、受控策略消融或与 WestlakeNLP 开展联合研究，请发送邮件至 **[liuzhenhao@westlake.edu.cn](mailto:liuzhenhao@westlake.edu.cn)** 简要说明研究用途与设想，我们将根据具体课题沟通合作方式。
