//! Rust 1.90 增强特性演示
//!
//! 本示例展示了Rust 1.90版本的最新语言特性在微服务开发中的应用，
//! 包括稳定的异步trait、GAT、TAIT等特性。

use microservice::prelude::*;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.90 增强特性演示");
    println!("================================");

    // 1. 演示增强的微服务
    demo_enhanced_microservice().await?;

    // 2. 演示异步迭代器
    demo_async_iterator().await?;

    // 3. 演示熔断器和限流器
    demo_circuit_breaker_and_rate_limiter().await?;

    // 4. 演示服务注册表
    demo_service_registry().await?;

    // 5. 演示数据处理器
    demo_data_processor().await?;

    println!("✅ 所有演示完成！");
    Ok(())
}

/// 演示增强的微服务
async fn demo_enhanced_microservice() -> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("\n📡 演示增强的微服务");
    println!("-------------------");

    // 创建增强的微服务实例
    let service = EnhancedServiceImpl::new("demo-service".to_string(), 10);

    // 创建测试请求
    let request = EnhancedServiceRequest {
        id: "test-request-1".to_string(),
        data: serde_json::json!({
            "operation": "success",
            "data": "Hello, Rust 1.90!"
        }),
        metadata: std::collections::HashMap::from([
            ("source".to_string(), "demo".to_string()),
            ("version".to_string(), "1.0.0".to_string()),
        ]),
        priority: Priority::High,
        timeout: Some(Duration::from_secs(30)),
    };

    // 处理请求
    let response = service.process_request(request).await?;
    println!("✅ 请求处理成功:");
    println!("   ID: {}", response.id);
    println!("   状态: {:?}", response.status);
    println!("   处理时间: {}ms", response.processing_time_ms);
    println!("   结果: {}", response.result);

    // 健康检查
    let health = service.health_check().await?;
    println!("✅ 服务健康状态:");
    println!("   服务名: {}", health.service);
    println!("   状态: {:?}", health.status);
    println!("   运行时间: {}秒", health.uptime_seconds);
    println!("   活跃请求: {}", health.active_requests);
    println!("   总请求数: {}", health.total_requests);
    println!("   错误率: {:.2}%", health.error_rate * 100.0);

    // 获取指标
    let metrics = service.get_metrics().await?;
    println!("✅ 服务指标:");
    println!("   每秒请求数: {:.2}", metrics.requests_per_second);
    println!("   平均响应时间: {:.2}ms", metrics.average_response_time_ms);
    println!("   错误率: {:.2}%", metrics.error_rate * 100.0);
    println!("   活跃连接: {}", metrics.active_connections);

    Ok(())
}

/// 演示异步迭代器
async fn demo_async_iterator() -> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("\n🔄 演示异步迭代器");
    println!("-------------------");

    // 创建测试请求
    let requests = vec![
        EnhancedServiceRequest {
            id: "req-1".to_string(),
            data: serde_json::json!({"type": "user", "action": "create"}),
            metadata: std::collections::HashMap::new(),
            priority: Priority::Normal,
            timeout: None,
        },
        EnhancedServiceRequest {
            id: "req-2".to_string(),
            data: serde_json::json!({"type": "order", "action": "update"}),
            metadata: std::collections::HashMap::new(),
            priority: Priority::High,
            timeout: None,
        },
        EnhancedServiceRequest {
            id: "req-3".to_string(),
            data: serde_json::json!({"type": "product", "action": "delete"}),
            metadata: std::collections::HashMap::new(),
            priority: Priority::Low,
            timeout: None,
        },
    ];

    // 创建请求流迭代器
    let mut stream = RequestStream::new(requests);

    println!("✅ 异步迭代器处理:");
    let mut count = 0;
    while let Some(request) = stream.next().await {
        count += 1;
        println!(
            "   处理请求 {}: ID={}, 优先级={:?}",
            count, request.id, request.priority
        );

        // 模拟处理延迟
        sleep(Duration::from_millis(100)).await;
    }

    println!("   总共处理了 {} 个请求", count);

    Ok(())
}

/// 演示熔断器和限流器
async fn demo_circuit_breaker_and_rate_limiter()
-> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 演示熔断器和限流器");
    println!("-------------------");

    // 演示熔断器
    println!("🔧 熔断器演示:");
    let mut circuit_breaker = EnhancedCircuitBreaker::new(3, Duration::from_secs(1));

    // 正常请求
    for i in 1..=2 {
        let result = circuit_breaker
            .call(|| {
                println!("   执行正常操作 {}", i);
                Ok(format!("success-{}", i))
            })
            .await;

        match result {
            Ok(msg) => println!("   ✅ 操作成功: {}", msg),
            Err(e) => println!("   ❌ 操作失败: {}", e),
        }
    }

    // 模拟失败请求
    for i in 1..=4 {
        let result = circuit_breaker
            .call(|| -> std::result::Result<String, EnhancedServiceError> {
                println!("   执行失败操作 {}", i);
                Err(EnhancedServiceError::ServiceUnavailable(
                    "模拟服务不可用".to_string(),
                ))
            })
            .await;

        match result {
            Ok(msg) => println!("   ✅ 操作成功: {}", msg),
            Err(e) => println!("   ❌ 操作失败: {}", e),
        }
    }

    // 演示限流器
    println!("\n🚦 限流器演示:");
    let mut rate_limiter = RateLimiter::new(3, Duration::from_millis(500));

    for i in 1..=5 {
        match rate_limiter.check_rate_limit().await {
            Ok(_) => println!("   ✅ 请求 {} 通过限流检查", i),
            Err(e) => println!("   ❌ 请求 {} 被限流: {}", i, e),
        }

        // 短暂延迟
        sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}

/// 演示服务注册表
async fn demo_service_registry() -> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示服务注册表");
    println!("-------------------");

    // 创建服务注册表
    let registry = EnhancedServiceRegistry::new();

    // 注册多个服务
    let services = vec![
        (
            "user-service",
            ServiceConfig {
                max_concurrent_requests: 50,
                circuit_breaker_threshold: 5,
                circuit_breaker_timeout_secs: 30,
                rate_limit_requests: 100,
                rate_limit_window_secs: 1,
            },
        ),
        (
            "order-service",
            ServiceConfig {
                max_concurrent_requests: 30,
                circuit_breaker_threshold: 3,
                circuit_breaker_timeout_secs: 20,
                rate_limit_requests: 80,
                rate_limit_window_secs: 1,
            },
        ),
        (
            "product-service",
            ServiceConfig {
                max_concurrent_requests: 100,
                circuit_breaker_threshold: 10,
                circuit_breaker_timeout_secs: 60,
                rate_limit_requests: 200,
                rate_limit_window_secs: 1,
            },
        ),
    ];

    println!("✅ 注册服务:");
    for (name, config) in services {
        registry.register_service(name.to_string(), config).await?;
        println!("   📝 已注册服务: {}", name);
    }

    // 列出所有服务
    let service_list = registry.list_services().await;
    println!("✅ 已注册的服务列表:");
    for service_name in service_list {
        println!("   🔧 {}", service_name);
    }

    // 获取特定服务
    if let Some(user_service) = registry.get_service("user-service").await {
        let health = user_service.health_check().await?;
        println!("✅ 用户服务健康状态:");
        println!("   状态: {:?}", health.status);
        println!("   运行时间: {}秒", health.uptime_seconds);
    }

    // 健康检查所有服务
    let all_health = registry.health_check_all().await;
    println!("✅ 所有服务健康状态:");
    for (name, health) in all_health {
        println!(
            "   {}: {:?} (运行{}秒)",
            name, health.status, health.uptime_seconds
        );
    }

    Ok(())
}

/// 演示数据处理器
async fn demo_data_processor() -> std::result::Result<(), Box<dyn std::error::Error>> {
    println!("\n🔄 演示数据处理器");
    println!("-------------------");

    // 创建数据处理器（函数式处理）
    let processor = AdvancedDataProcessor::<String>::new();

    // 处理单个数据
    let input = "Hello, Rust 1.90!";
    let result = processor
        .process_data(input.to_string(), |s: String| {
            let upper = s.to_uppercase();
            let reversed: String = upper.chars().rev().collect();
            Ok(format!("{} (长度: {})", reversed.clone(), reversed.len()))
        })
        .await?;
    println!("✅ 数据处理结果:");
    println!("   输入: {}", input);
    println!("   输出: {}", result);

    // 批量处理数据
    let batch_input = vec![
        "rust".to_string(),
        "microservice".to_string(),
        "async".to_string(),
        "performance".to_string(),
    ];

    let batch_result = processor
        .process_batch(batch_input.clone(), |s: String| {
            let upper = s.to_uppercase();
            let reversed: String = upper.chars().rev().collect();
            Ok(format!("{} (长度: {})", reversed.clone(), reversed.len()))
        })
        .await?;
    println!("✅ 批量数据处理结果:");
    for (input, output) in batch_input.iter().zip(batch_result.iter()) {
        println!("   {} -> {}", input, output);
    }

    Ok(())
}

// 处理器以闭包形式传入，无需定义具体处理器类型
