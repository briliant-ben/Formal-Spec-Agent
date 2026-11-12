# Formal-Spec-Agent

可复用的规范建模与验证框架。当前提供一个可执行的初始核心，支持：

**规范与范围绑定 → Protocol IR → 参考执行／独立 Z3 → 测试生成 → IR生成独立C → 执行轨迹 → 差异与规范追溯**。

协议逻辑只在声明式 IR 中表达。模型供应商、MCP、Skill 或外部多Agent harness 是可替换调用方；它们的自评不能替代验收。这里还不是任意英文规范到完整协议的全自动系统。

[TCPIP-Model](https://github.com/briliant-ben/TCPIP-Model) 保存 TCP/IP 模型、RFC绑定、原始实验记录、PCAP 和 Linux/lwIP 适配器。此仓库统一维护后续通用语义和执行器；提取来源与必要的边界改动见 [provenance/extraction.json](provenance/extraction.json)。

## 安装与离线运行

需要 Python3.11+、POSIX系统和 C99编译器。Z3版本固定，离线验收不需要API密钥、网络权限或现有协议栈。

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -e .
.venv/bin/python -m unittest discover -s tests -v
```

自带示例是**非网络的有限字节邮箱**，规范、字面量种子和探索域全部预先绑定。输出目录必须全新，位于工具目录外：

```sh
TASK_SHA=$(shasum -a 256 examples/mailbox/task.json | cut -d ' ' -f 1)
.venv/bin/formal-spec-agent run examples/mailbox/task.json \
  --workspace examples/mailbox --task-sha256 "$TASK_SHA" --out /tmp/mailbox-run-001
.venv/bin/formal-spec-agent verify /tmp/mailbox-run-001 \
  --workspace examples/mailbox --task-sha256 "$TASK_SHA"
```

命令中的本地摘要只是版本绑定；生产使用时批准的摘要由独立控制器提供。返回0表示该声明切片通过，1表示未决或失败，2表示输入／证据拒绝。`UNKNOWN` 和不支持的语义必须显式报告。单独一次测试、规则覆盖或有界检查都不是完整规范／编译器证明。

外部协议数据无需复制到本仓库：

```sh
.venv/bin/formal-spec-agent run /path/to/TCPIP-Model/flows/tcp-active-open.json \
  --workspace /path/to/TCPIP-Model --task-sha256 APPROVED_TASK_SHA --out /tmp/tcp-framework-001
```

原型完整字节布局由IR生成。旧TCP专用 `wire` codec未迁入通用核心，若请求它会明确拒绝；既有TCP网络通道继续在基准仓库中复现。

## 可选模型角色

`formal-spec-agent propose` 同时启动一至四个独立 JSON 提案角色，使用固定源文件／job摘要和原共享请求台账。当前附带 DeepSeek adapter；模型名称必须显式指定。它**不会执行模型返回的代码、修改模型／oracle、自动重试失败付费请求或自动批准协议**。

```sh
.venv/bin/formal-spec-agent propose --job /candidate/job.json --workspace /candidate \
  --job-sha256 APPROVED_JOB_SHA --out /runs/proposal-001 \
  --ledger /private/shared-ledger --credential-file /private/deepseek.key --model YOUR_MODEL
```

输出 `requires_controller_review` 仅表示提案已收到，之后应由控制器审查并通过 `run`／`verify`。凭据、台账和输出必须位于候选工作区之外。默认有调用数限制；明确授权时可用 `--uncapped-calls`，仍沿用同一台账。见 [角色与信任边界](docs/agent-contract.md)。测试只使用假的 provider，不产生API费用。

## 仓库边界与范围

[迁移说明](docs/extraction.md)记录唯一维护源、冻结旧执行器、固定Git客户端、历史checker与新运行记录的区别。阶段性的独立命题、字节缓冲容量、有界深度和当前C后端限制不因更换仓库而扩大。适配其他协议需要单独提交规范版本、范围、IR和独立验收条件；本次没有迁移TCP模型、网络证据、密钥、虚拟环境或编译二进制。
