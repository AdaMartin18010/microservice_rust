//! 简化微服务演示
//!
//! 这个示例展示了简化的微服务功能，避免了复杂的 trait 对象问题

use anyhow::Result;
use tokio::time::{Duration, sleep};

// 导入我们的简化微服务模块
use microservice::simple_microservice::*;

/// 简化微服务演示管理器
pub struct SimpleMicroserviceDemoManager {
    manager: SimpleMicroserviceManager,
}

impl SimpleMicroserviceDemoManager {
    pub fn new() -> Self {
        let config = SimpleConfig {
            service_name: "demo-microservice".to_string(),
            port: 8080,
            host: "127.0.0.1".to_string(),
            max_connections: 1000,
        };

        Self {
            manager: SimpleMicroserviceManager::new(config),
        }
    }

    /// 演示基本的微服务功能
    pub async fn demo_basic_functionality(&self) -> Result<()> {
        println!("\n🚀 演示基本微服务功能:");
        println!("================================");

        // 启动微服务
        self.manager.start().await?;

        // 模拟处理请求
        let user_service = SimpleUserService::new();
        let request = SimpleRequest {
            id: "demo-1".to_string(),
            data: "Hello, Microservice!".to_string(),
            timestamp: chrono::Utc::now(),
        };

        let response = user_service.process_request(request).await?;
        println!("处理请求: {}", response.result);

        // 健康检查
        let health = user_service.health_check().await?;
        println!("健康状态: {}", health.status);

        Ok(())
    }

    /// 演示服务注册和发现
    pub async fn demo_service_registry(&self) -> Result<()> {
        println!("\n📋 演示服务注册和发现:");
        println!("================================");

        let registry = SimpleServiceRegistry::new();

        // 注册多个服务
        let user_service = SimpleUserService::new();
        registry
            .register("user-service".to_string(), Box::new(user_service))
            .await?;

        println!("✅ 服务注册完成");

        // 尝试获取服务
        if registry.has_service("user-service").await {
            println!("✅ 服务发现成功");
        } else {
            println!("❌ 服务发现失败");
        }

        Ok(())
    }

    /// 演示性能监控
    pub async fn demo_performance_monitoring(&self) -> Result<()> {
        println!("\n📊 演示性能监控:");
        println!("================================");

        let monitor = SimplePerformanceMonitor::new();

        // 记录一些性能指标
        monitor
            .record_metric("request_count".to_string(), 100.0)
            .await?;
        monitor
            .record_metric("response_time_ms".to_string(), 50.0)
            .await?;
        monitor
            .record_metric("error_rate".to_string(), 0.01)
            .await?;
        monitor.record_metric("cpu_usage".to_string(), 75.5).await?;
        monitor
            .record_metric("memory_usage_mb".to_string(), 512.0)
            .await?;

        println!("✅ 性能指标记录完成");

        // 获取并显示指标
        let metrics = self.manager.get_metrics().await;
        println!("当前指标:");
        for (name, value) in metrics {
            println!("  - {}: {}", name, value);
        }

        // 获取特定指标
        if let Some(cpu_usage) = monitor.get_metric("cpu_usage").await {
            println!("CPU 使用率: {}%", cpu_usage);
        }

        Ok(())
    }

    /// 演示配置管理
    pub async fn demo_configuration_management(&self) -> Result<()> {
        println!("\n⚙️ 演示配置管理:");
        println!("================================");

        // 创建不同的配置
        let configs = vec![
            SimpleConfig {
                service_name: "user-service".to_string(),
                port: 8081,
                host: "127.0.0.1".to_string(),
                max_connections: 500,
            },
            SimpleConfig {
                service_name: "order-service".to_string(),
                port: 8082,
                host: "127.0.0.1".to_string(),
                max_connections: 1000,
            },
            SimpleConfig {
                service_name: "payment-service".to_string(),
                port: 8083,
                host: "127.0.0.1".to_string(),
                max_connections: 2000,
            },
        ];

        for config in configs {
            println!("服务配置:");
            println!("  名称: {}", config.service_name);
            println!("  端口: {}", config.port);
            println!("  主机: {}", config.host);
            println!("  最大连接数: {}", config.max_connections);
            println!();
        }

        Ok(())
    }

    /// 演示错误处理
    pub async fn demo_error_handling(&self) -> Result<()> {
        println!("\n⚠️ 演示错误处理:");
        println!("================================");

        let user_service = SimpleUserService::new();

        // 模拟正常请求
        let normal_request = SimpleRequest {
            id: "normal-1".to_string(),
            data: "正常请求".to_string(),
            timestamp: chrono::Utc::now(),
        };

        match user_service.process_request(normal_request).await {
            Ok(response) => println!("✅ 正常请求处理成功: {}", response.result),
            Err(e) => println!("❌ 正常请求处理失败: {}", e),
        }

        // 模拟异常请求（空数据）
        let empty_request = SimpleRequest {
            id: "empty-1".to_string(),
            data: "".to_string(),
            timestamp: chrono::Utc::now(),
        };

        match user_service.process_request(empty_request).await {
            Ok(response) => println!("✅ 空请求处理成功: {}", response.result),
            Err(e) => println!("❌ 空请求处理失败: {}", e),
        }

        Ok(())
    }

    /// 演示并发处理
    #[allow(unused_variables)]
    pub async fn demo_concurrent_processing(&self) -> Result<()> {
        println!("\n⚡ 演示并发处理:");
        println!("================================");

        let user_service = SimpleUserService::new();

        // 创建多个并发请求
        let mut handles = Vec::new();

        for i in 0..5 {
            let service = SimpleUserService::new();
            let handle = tokio::spawn(async move {
                let request = SimpleRequest {
                    id: format!("concurrent-{}", i),
                    data: format!("并发请求 {}", i),
                    timestamp: chrono::Utc::now(),
                };

                match service.process_request(request).await {
                    Ok(response) => println!("✅ 并发请求 {} 处理成功: {}", i, response.result),
                    Err(e) => println!("❌ 并发请求 {} 处理失败: {}", i, e),
                }
            });

            handles.push(handle);
        }

        // 等待所有请求完成
        for handle in handles {
            let _ = handle.await;
        }

        println!("✅ 所有并发请求处理完成");

        Ok(())
    }

    /// 演示微服务生命周期
    pub async fn demo_microservice_lifecycle(&self) -> Result<()> {
        println!("\n🔄 演示微服务生命周期:");
        println!("================================");

        // 启动
        println!("1. 启动微服务...");
        self.manager.start().await?;

        // 运行一段时间
        println!("2. 微服务运行中...");
        sleep(Duration::from_millis(100)).await;

        // 获取指标
        println!("3. 获取运行指标...");
        let metrics = self.manager.get_metrics().await;
        println!("   指标数量: {}", metrics.len());

        // 停止
        println!("4. 停止微服务...");
        self.manager.stop().await?;

        println!("✅ 微服务生命周期演示完成");

        Ok(())
    }

    /// 演示最佳实践
    pub async fn demo_best_practices(&self) -> Result<()> {
        println!("\n📚 演示最佳实践:");
        println!("================================");

        println!("微服务开发最佳实践:");
        println!();

        println!("🚀 服务设计:");
        println!("  ✅ 单一职责原则");
        println!("  ✅ 松耦合设计");
        println!("  ✅ 高内聚实现");
        println!("  ✅ 清晰的接口定义");
        println!();

        println!("📊 监控和观测:");
        println!("  ✅ 性能指标收集");
        println!("  ✅ 健康检查机制");
        println!("  ✅ 错误日志记录");
        println!("  ✅ 分布式追踪");
        println!();

        println!("🔧 配置管理:");
        println!("  ✅ 环境特定配置");
        println!("  ✅ 动态配置更新");
        println!("  ✅ 配置验证");
        println!("  ✅ 敏感信息保护");
        println!();

        println!("🛡️ 错误处理:");
        println!("  ✅ 优雅的错误处理");
        println!("  ✅ 重试机制");
        println!("  ✅ 熔断器模式");
        println!("  ✅ 超时控制");
        println!();

        println!("⚡ 性能优化:");
        println!("  ✅ 异步处理");
        println!("  ✅ 连接池管理");
        println!("  ✅ 缓存策略");
        println!("  ✅ 资源限制");
        println!();

        println!("🔒 安全考虑:");
        println!("  ✅ 身份认证");
        println!("  ✅ 授权控制");
        println!("  ✅ 数据加密");
        println!("  ✅ 安全传输");

        Ok(())
    }
}

impl Default for SimpleMicroserviceDemoManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 主函数演示简化微服务
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 简化微服务演示");
    println!("================================");

    // 创建简化微服务演示管理器
    let demo_manager = SimpleMicroserviceDemoManager::new();

    // 演示基本功能
    demo_manager.demo_basic_functionality().await?;

    // 演示服务注册和发现
    demo_manager.demo_service_registry().await?;

    // 演示性能监控
    demo_manager.demo_performance_monitoring().await?;

    // 演示配置管理
    demo_manager.demo_configuration_management().await?;

    // 演示错误处理
    demo_manager.demo_error_handling().await?;

    // 演示并发处理
    demo_manager.demo_concurrent_processing().await?;

    // 演示微服务生命周期
    demo_manager.demo_microservice_lifecycle().await?;

    // 演示最佳实践
    demo_manager.demo_best_practices().await?;

    println!("\n✅ 简化微服务演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 简化的服务接口设计");
    println!("- 基本的服务注册和发现");
    println!("- 性能指标监控");
    println!("- 配置管理");
    println!("- 错误处理机制");
    println!("- 并发处理支持");
    println!("- 微服务生命周期管理");
    println!();
    println!("📚 技术价值:");
    println!("- 避免复杂的 trait 对象问题");
    println!("- 清晰的代码结构");
    println!("- 易于理解和维护");
    println!("- 良好的测试覆盖");
    println!("- 实用的最佳实践");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_functionality() {
        let demo_manager = SimpleMicroserviceDemoManager::new();
        let result = demo_manager.demo_basic_functionality().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_service_registry() {
        let demo_manager = SimpleMicroserviceDemoManager::new();
        let result = demo_manager.demo_service_registry().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_performance_monitoring() {
        let demo_manager = SimpleMicroserviceDemoManager::new();
        let result = demo_manager.demo_performance_monitoring().await;
        assert!(result.is_ok());
    }
}
