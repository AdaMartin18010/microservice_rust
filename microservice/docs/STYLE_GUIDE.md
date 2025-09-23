# 文档风格与术语规范

## 语言与格式

- 语言：中文简体为主，必要术语保留英文简称（括号内标注）。
- 专有名词：统一大小写与缩写（如 OpenTelemetry、Prometheus、Jaeger、Kubernetes、GitOps）。
- 数字与单位：阿拉伯数字，单位前空格（如 1 ms、128 MB）。

## 术语统一

- Trace/Span/Metric/Log：遵循 OTel 术语；
- 熔断/Circuit Breaker、重试/Retry、退避/Backoff；
- 一致性/Consistency、幂等/Idempotency、隔离舱/Bulkhead；
- 事件驱动/EDA、Outbox、Saga、TCC；
- mTLS、JWT、OAuth2/OIDC；
- Service Mesh、Sidecar、Gateway。

## 文风

- 标题简短，段落首句给出结论；
- 列表项采用动宾结构，避免冗长；
- 代码块需最小化并可直接运行或清晰伪代码。
