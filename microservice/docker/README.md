# Docker Compose 模板

本目录提供快速拉起微服务依赖的 Docker Compose 模板。

## 观测栈

```bash
# 启动观测栈 (Prometheus + Grafana + Tempo + Loki + OTel Collector)
docker-compose -f docker-compose.observability.yml up -d

# 访问地址
# Grafana: http://localhost:3000 (admin/admin)
# Prometheus: http://localhost:9090
# Tempo: http://localhost:3200
```

## 消息队列栈

```bash
# 启动消息队列 (Kafka + NATS + Redis + Debezium)
docker-compose -f docker-compose.messaging.yml up -d

# 访问地址
# Kafka: localhost:9092
# NATS: localhost:4222 (monitoring: localhost:8222)
# Redis: localhost:6379
# Debezium Connect: http://localhost:8083
```

## 配置说明

- 观测栈配置：`otel-collector.yml`, `prometheus.yml`, `tempo.yaml`, `loki.yml`
- 消息栈配置：Kafka 自动创建主题，NATS 启用 JetStream
- 数据持久化：Redis 数据卷，Grafana 仪表盘持久化

## 与示例集成

启动相应栈后，运行 Rust 示例：

```bash
# 观测示例
cargo run --example standalone_observability_demo

# 消息示例  
cargo run --example messaging_demo
cargo run --example messaging_advanced_demo
```
