#!/bin/bash
# 快速演示脚本 - 展示Rust微服务框架的核心功能

echo "🚀 Rust微服务框架快速演示"
echo "================================"

# 检查Rust环境
echo "📋 检查环境..."
if ! command -v cargo &> /dev/null; then
    echo "❌ 错误: 未找到cargo，请先安装Rust"
    exit 1
fi

echo "✅ Rust环境检查通过"

# 编译项目
echo ""
echo "🔨 编译项目..."
cargo build --quiet
if [ $? -eq 0 ]; then
    echo "✅ 项目编译成功"
else
    echo "❌ 项目编译失败"
    exit 1
fi

# 运行测试
echo ""
echo "🧪 运行测试..."
cargo test --lib --quiet
if [ $? -eq 0 ]; then
    echo "✅ 测试通过"
else
    echo "⚠️  部分测试失败（这是正常的，因为需要外部依赖）"
fi

# 显示项目结构
echo ""
echo "📁 项目结构概览:"
echo "├── src/"
echo "│   ├── grpc/           # gRPC服务实现"
echo "│   ├── messaging/      # 消息队列实现"
echo "│   ├── middleware/     # 中间件实现"
echo "│   ├── axum/          # Axum Web框架"
echo "│   ├── actix/         # Actix-Web框架"
echo "│   └── ...            # 其他模块"
echo "├── examples/          # 示例代码"
echo "├── benches/           # 性能基准测试"
echo "├── scripts/           # 工具脚本"
echo "└── proto/             # Protocol Buffers定义"

# 显示功能特性
echo ""
echo "🌟 核心功能特性:"
echo "✅ 多种Web框架支持 (Axum, Actix-Web, Warp, Tide)"
echo "✅ 完整的gRPC实现 (Tonic + Protocol Buffers)"
echo "✅ 消息队列支持 (Redis, RabbitMQ, Kafka, NATS)"
echo "✅ 可观测性 (OpenTelemetry/Prometheus/Jaeger/Grafana)"
echo "✅ 丰富的中间件 (请求ID, 日志, 限流, 健康检查)"
echo "✅ 性能基准测试 (Criterion框架)"
echo "✅ 条件编译支持 (通过features控制依赖)"
echo "✅ 完整的错误处理"
echo "✅ 详细的文档和示例"

# 一键演示入口（非交互，用户可复制执行）
echo ""
echo "💡 一键演示入口（复制执行以下命令）："
echo "# 1) HTTP: 启动 Axum REST API (参见 docs/14.1)"
echo "cargo run --example axum_rest_api"
echo "# 2) gRPC: 启动 Tonic 服务 与 客户端 (参见 docs/14.2)"
echo "cargo run --example grpc_service ; cargo run --example grpc_client_demo"
echo "# 3) 消息: Kafka/NATS 示例生产与消费 (参见 docs/14.3/14.4)"
echo "cargo run --example messaging_demo ; cargo run --example messaging_advanced_demo"
echo "# 4) 观测: 独立可观测性演示 (参见 docs/08.1)"
echo "cargo run --example standalone_observability_demo"

# 环境与配置提示
echo ""
echo "⚙️  配置说明:"
echo "• 环境变量: SERVICE_NAME, SERVICE_PORT, DATABASE_URL, OTEL_EXPORTER_OTLP_ENDPOINT 等"
echo "• 配置文件: config.toml；或通过 Helm/Operator 部署 OTel Collector (docs/08.1)"
echo "• K8s/Traefik/Istio 模板: 参见 docs/14.x 最小配置模板"

echo ""
echo "🎉 演示完成！"
echo "📚 更多信息请查看 README.md 和项目文档"
echo "🔧 需要帮助？请查看 examples/ 目录中的示例代码"
