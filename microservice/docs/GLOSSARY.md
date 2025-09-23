# 术语表（Glossary）

- Async Trait：支持 `async fn` 的 trait，用于异步接口抽象。
- GAT（Generic Associated Types）：泛型关联类型，改进生命周期与借用表达能力。
- TAIT：Type Alias Impl Trait 的简称，此处以 `Pin<Box<dyn Future>>` 替代。
- OTel（OpenTelemetry）：统一 Traces/Metrics/Logs 规范与实现。
- RED 指标：Rate/Error/Duration，面向请求的观测指标集。
- USE 指标：Utilization/Saturation/Errors，面向资源的观测指标集。
- EDA（Event-Driven Architecture）：事件驱动架构。
- Outbox：本地事务表，保证事件与状态更改的一致性。
- Saga：长事务的分布式协调与补偿方案。
- Bulkhead（隔离舱）：将资源隔离以防止故障扩散。
- mTLS：双向 TLS。
- JWKS：JSON Web Key Set，OIDC 公钥分发。
- GitOps：以 Git 作为声明式配置的唯一事实来源，自动化交付。
