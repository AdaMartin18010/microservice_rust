//! 现代微服务框架演示
//!
//! 本示例展示了如何使用最新的 Rust 微服务框架：
//! - Poem: 现代化 Web 框架
//! - Salvo: 功能强大的 Web 框架
//! - Volo: 字节跳动高性能 RPC 框架
//! - fusen-rs: 跨语言微服务框架
//! - Spring-rs: Spring Boot 风格的 Rust 框架

use anyhow::Result;
use std::collections::HashMap;
use tokio::time::{Duration, sleep};

// 导入我们的现代框架模块
use microservice::modern_frameworks::*;

/// 框架演示管理器
pub struct FrameworkDemoManager {
    services: HashMap<String, Box<dyn ModernFramework + Send + Sync>>,
}

impl FrameworkDemoManager {
    pub fn new() -> Self {
        Self {
            services: HashMap::new(),
        }
    }

    /// 注册所有可用的框架服务
    pub fn register_all_frameworks(&mut self) -> Result<()> {
        let available_frameworks = FrameworkFactory::get_available_frameworks();
        println!("可用框架: {:?}", available_frameworks);

        // 注册 Poem 服务
        #[cfg(feature = "with-poem")]
        {
            let poem_service = FrameworkFactory::create_poem_service();
            self.services.insert("Poem".to_string(), poem_service);
            println!("✅ Poem 框架已注册");
        }

        // 注册 Salvo 服务
        #[cfg(feature = "with-salvo")]
        {
            let salvo_service = FrameworkFactory::create_salvo_service();
            self.services.insert("Salvo".to_string(), salvo_service);
            println!("✅ Salvo 框架已注册");
        }

        // 注册 Volo 服务
        #[cfg(feature = "with-volo")]
        {
            let volo_service = FrameworkFactory::create_volo_service();
            self.services.insert("Volo".to_string(), volo_service);
            println!("✅ Volo 框架已注册");
        }

        // 注册 fusen-rs 服务
        #[cfg(feature = "with-fusen")]
        {
            let fusen_service = FrameworkFactory::create_fusen_service();
            self.services.insert("fusen-rs".to_string(), fusen_service);
            println!("✅ fusen-rs 框架已注册");
        }

        // 注册 Spring-rs 服务
        #[cfg(feature = "with-spring-rs")]
        {
            let spring_rs_service = FrameworkFactory::create_spring_rs_service();
            self.services
                .insert("Spring-rs".to_string(), spring_rs_service);
            println!("✅ Spring-rs 框架已注册");
        }

        Ok(())
    }

    /// 演示框架健康检查
    pub async fn demo_health_checks(&self) -> Result<()> {
        println!("\n🏥 演示框架健康检查:");
        println!("================================");

        for (name, service) in &self.services {
            match service.health_check().await {
                Ok(health) => {
                    println!("{} 健康状态: {}", name, health.status);
                    println!("  - 版本: {}", health.version);
                    println!("  - 运行时间: {} 秒", health.uptime);
                    println!("  - 时间戳: {}", health.timestamp);
                }
                Err(e) => {
                    println!("{} 健康检查失败: {}", name, e);
                }
            }
            println!();
        }

        Ok(())
    }

    /// 演示框架指标
    pub async fn demo_metrics(&self) -> Result<()> {
        println!("\n📊 演示框架指标:");
        println!("================================");

        for (name, service) in &self.services {
            match service.get_metrics().await {
                Ok(metrics) => {
                    println!("{} 指标:", name);
                    println!("  - 总请求数: {}", metrics.requests_total);
                    println!("  - 活跃连接数: {}", metrics.active_connections);
                    println!("  - 内存使用: {:.2} MB", metrics.memory_usage_mb);
                    println!("  - CPU 使用率: {:.2}%", metrics.cpu_usage_percent);
                    println!("  - 平均响应时间: {:.2} ms", metrics.response_time_avg_ms);
                }
                Err(e) => {
                    println!("{} 获取指标失败: {}", name, e);
                }
            }
            println!();
        }

        Ok(())
    }

    /// 演示性能比较
    pub async fn demo_performance_comparison(&self) -> Result<()> {
        println!("\n⚡ 演示性能比较:");
        println!("================================");

        let performance_metrics = FrameworkComparator::compare_performance();

        for (framework, metrics) in performance_metrics {
            println!("{} 性能指标:", framework);
            println!("  - 吞吐量: {} RPS", metrics.throughput_rps);
            println!("  - P50 延迟: {:.2} ms", metrics.latency_p50_ms);
            println!("  - P95 延迟: {:.2} ms", metrics.latency_p95_ms);
            println!("  - P99 延迟: {:.2} ms", metrics.latency_p99_ms);
            println!("  - 内存使用: {:.2} MB", metrics.memory_usage_mb);
            println!("  - CPU 使用率: {:.2}%", metrics.cpu_usage_percent);
            println!();
        }

        Ok(())
    }

    /// 演示框架启动和停止
    pub async fn demo_start_stop(&self) -> Result<()> {
        println!("\n🚀 演示框架启动和停止:");
        println!("================================");

        for (name, service) in &self.services {
            println!("演示 {} 框架:", name);

            // 模拟启动服务
            match service.start(8080).await {
                Ok(_) => println!("  ✅ {} 服务启动成功", name),
                Err(e) => println!("  ❌ {} 服务启动失败: {}", name, e),
            }

            // 等待一段时间
            sleep(Duration::from_millis(100)).await;

            // 模拟停止服务
            match service.stop().await {
                Ok(_) => println!("  ✅ {} 服务停止成功", name),
                Err(e) => println!("  ❌ {} 服务停止失败: {}", name, e),
            }

            println!();
        }

        Ok(())
    }

    /// 演示并发处理
    pub async fn demo_concurrent_processing(&self) -> Result<()> {
        println!("\n⚡ 演示并发处理:");
        println!("================================");

        let handles: Vec<_> = self
            .services
            .iter()
            .map(|(name, service)| {
                let name = name.clone();
                tokio::spawn(async move {
                    let start = std::time::Instant::now();

                    // 模拟并发健康检查
                    let health_result = service.health_check().await;
                    let health_time = start.elapsed().as_millis();

                    // 模拟并发指标获取
                    let metrics_result = service.get_metrics().await;
                    let metrics_time = start.elapsed().as_millis();

                    println!("{} 并发处理结果:", name);
                    match health_result {
                        Ok(health) => println!("  - 健康检查: 成功 ({}ms)", health_time),
                        Err(e) => println!("  - 健康检查: 失败 - {}", e),
                    }

                    match metrics_result {
                        Ok(metrics) => println!(
                            "  - 指标获取: 成功 ({}ms) - 请求数: {}",
                            metrics_time, metrics.requests_total
                        ),
                        Err(e) => println!("  - 指标获取: 失败 - {}", e),
                    }

                    println!();
                })
            })
            .collect();

        // 等待所有并发任务完成
        for handle in handles {
            handle.await?;
        }

        Ok(())
    }

    /// 演示框架选择建议
    pub async fn demo_framework_recommendations(&self) -> Result<()> {
        println!("\n💡 框架选择建议:");
        println!("================================");

        println!("根据使用场景选择框架:");
        println!();

        println!("🚀 高性能场景 (推荐 Volo):");
        println!("  - 需要极致性能的 RPC 服务");
        println!("  - 字节跳动内部验证的高性能框架");
        println!("  - 适合大规模微服务架构");
        println!();

        println!("🌐 现代化 Web API (推荐 Poem):");
        println!("  - 构建现代化的 RESTful API");
        println!("  - 需要 OpenAPI 文档生成");
        println!("  - 追求简洁优雅的代码风格");
        println!();

        println!("🏢 企业级应用 (推荐 Salvo):");
        println!("  - 功能丰富的企业级 Web 应用");
        println!("  - 需要完整的中间件支持");
        println!("  - 适合复杂的业务逻辑处理");
        println!();

        println!("🌍 跨语言服务 (推荐 fusen-rs):");
        println!("  - 需要与 Java 服务集成");
        println!("  - 兼容 Dubbo3 和 SpringCloud");
        println!("  - 多语言微服务架构");
        println!();

        println!("☕ Spring Boot 风格 (推荐 Spring-rs):");
        println!("  - 从 Java Spring Boot 迁移");
        println!("  - 熟悉 Spring 生态的团队");
        println!("  - 需要依赖注入和配置管理");
        println!();

        Ok(())
    }
}

/// 主函数演示现代微服务框架
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 现代微服务框架演示");
    println!("================================");

    // 创建框架演示管理器
    let mut demo_manager = FrameworkDemoManager::new();

    // 注册所有可用的框架
    println!("\n📋 注册框架:");
    demo_manager.register_all_frameworks()?;

    if demo_manager.services.is_empty() {
        println!("⚠️  没有可用的框架，请确保启用了相应的 feature 标志");
        println!("可用的 feature 标志:");
        println!("  - with-poem");
        println!("  - with-salvo");
        println!("  - with-volo");
        println!("  - with-fusen");
        println!("  - with-spring-rs");
        println!();
        println!("使用方法:");
        println!("  cargo run --example modern_frameworks_demo --features with-poem,with-salvo");
        return Ok(());
    }

    // 演示框架健康检查
    demo_manager.demo_health_checks().await?;

    // 演示框架指标
    demo_manager.demo_metrics().await?;

    // 演示性能比较
    demo_manager.demo_performance_comparison().await?;

    // 演示框架启动和停止
    demo_manager.demo_start_stop().await?;

    // 演示并发处理
    demo_manager.demo_concurrent_processing().await?;

    // 演示框架选择建议
    demo_manager.demo_framework_recommendations().await?;

    println!("✅ 现代微服务框架演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 支持 5 个最新的 Rust 微服务框架");
    println!("- 统一的框架接口和抽象");
    println!("- 完整的健康检查和指标监控");
    println!("- 性能比较和选择建议");
    println!("- 并发处理和异步优化");
    println!("- 企业级功能和中间件支持");
    println!();
    println!("📚 更多信息:");
    println!("- Poem: https://poem.rs/");
    println!("- Salvo: https://salvo.rs/");
    println!("- Volo: https://volo-rs.github.io/");
    println!("- fusen-rs: https://github.com/fusen-rs/fusen-rs");
    println!("- Spring-rs: https://github.com/spring-rs/spring-rs");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_framework_demo_manager() {
        let mut demo_manager = FrameworkDemoManager::new();
        let result = demo_manager.register_all_frameworks();
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_performance_comparison() {
        let performance_metrics = FrameworkComparator::compare_performance();
        assert!(!performance_metrics.is_empty());

        for (framework, metrics) in performance_metrics {
            assert!(metrics.throughput_rps > 0);
            assert!(metrics.latency_p50_ms > 0.0);
            assert!(metrics.memory_usage_mb > 0.0);
        }
    }

    #[tokio::test]
    async fn test_available_frameworks() {
        let frameworks = FrameworkFactory::get_available_frameworks();
        // 根据启用的 feature 检查框架数量
        assert!(!frameworks.is_empty());
    }
}
