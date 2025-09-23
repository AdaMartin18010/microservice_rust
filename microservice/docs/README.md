# Rust 1.90 微服务指南（总览）

本目录提供基于 Rust 1.90 与 2025 年技术生态的微服务完整实践指南：框架选型、服务治理、数据与消息、观测、安全、部署、性能与最佳实践。

## 如何使用本指南

- 快速入门：先读 1.x 与 3.x（Axum/Actix/Tonic）
- 落地治理：4.x 服务发现、5.x 网关、8.x 可观测性、9.x 安全
- 工程化：6.x 数据、7.x 事件驱动、10.x 部署、11.x 性能
- 架构方法：12.x 最佳实践、13.x 前沿趋势

## 快速开始

- 前置要求：已安装 Rust 1.70+（建议 1.90）、`protoc`、Docker（可选）
- 克隆并构建

```bash
git clone https://example.com/microservice_rust.git
cd microservice/microservice
cargo build
```

- 一键体验（示例/基准/文档校验）

```bash
# Windows PowerShell
./scripts/quick_demo.ps1
./scripts/run_benchmarks.ps1
./scripts/verify_docs.ps1

# Linux/macOS
bash scripts/quick_demo.sh
bash scripts/run_benchmarks.sh
bash scripts/verify_docs.sh
```

## 运行示例

- 位置：`examples/`（Axum/Actix/Tonic/可观测性/性能优化等）
- 运行方式：

```bash
cargo run --example advanced_comprehensive_demo
cargo run --example rust_190_enhanced_demo
cargo run --example performance_optimization_demo
```

提示：部分示例需要本地依赖（如 Kafka/Redis/Jaeger），可参考 `docker/` 与 `k8s/` 下的编排文件快速启动依赖。

## 运行基准测试

- 位置：`benches/`（Axum、gRPC、消息队列、综合基准）
- 运行方式：

```bash
cargo bench
# 或使用脚本（包含环境准备与参数）
./scripts/run_benchmarks.ps1   # Windows
bash scripts/run_benchmarks.sh # Linux/macOS
```

## 仓库结构速览

- `src/`：核心库与模块（框架、消息、观测、安全、性能等）
- `examples/`：可直接运行的示例集合
- `benches/`：性能基准场景
- `docker/`、`k8s/`：本地与云原生编排
- `scripts/`：一键演示、校验、基准与工具脚本
- `docs/`：本指南与各专题文档

## 推荐组合方案（按场景）

- 互联网 API：axum + SQLx + Redis + Kafka + Kong + OTel
- 企业内部 RPC：tonic + Volo（混合）+ etcd/Consul + Traefik + OTel
- 高吞吐边缘：Actix-Web + NATS + ClickHouse + Traefik + OTel
- 云原生全家桶：K8s + Service Mesh + GitOps + OTel/Grafana

## 关键参考

- 02 Rust 1.90：异步/GAT/TAIT 替代与工程模式
- 07 事件驱动：Outbox、Saga、一致性与可回放
- 08 可观测性：统一 Traces/Metrics/Logs 与采样策略
- 11 性能：基准、背压、并发优化与压测方法

## 附录

- 术语表：`./GLOSSARY.md`
- 链接校验：`../scripts/linkcheck.sh` 或 `../scripts/linkcheck.ps1`
- 一键验证：`../scripts/verify_docs.sh` 或 `../scripts/verify_docs.ps1`

---

如需按照你的业务定制方案，可从 12.1 的模式清单开始，结合 6/7/8/9/10/11 章节裁剪。
