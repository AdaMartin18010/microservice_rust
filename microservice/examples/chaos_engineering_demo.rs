//! 混沌工程演示
//!
//! 本示例展示了混沌工程功能：
//! - 故障注入 (Fault Injection)
//! - 混沌实验 (Chaos Experiments)
//! - 弹性测试 (Resilience Testing)
//! - 混沌猴子 (Chaos Monkey)

use anyhow::Result;
use std::collections::HashMap;
use tokio::time::{Duration, sleep};

// 导入我们的混沌工程模块
use microservice::chaos_engineering::*;

/// 混沌工程演示管理器
pub struct ChaosEngineeringDemoManager {
    service: AdvancedChaosEngineeringService,
}

impl ChaosEngineeringDemoManager {
    pub fn new() -> Self {
        let config = ChaosConfig {
            enable_chaos_monkey: true,
            failure_rate: 0.1,        // 10% failure rate
            experiment_duration: 300, // 5 minutes
            recovery_timeout: 60,     // 1 minute
            max_concurrent_experiments: 3,
            enable_auto_recovery: true,
            monitoring_enabled: true,
        };

        let service = ChaosEngineeringServiceFactory::create_custom_service(config);
        Self { service }
    }

    /// 演示故障注入
    pub async fn demo_fault_injection(&self) -> Result<()> {
        println!("\n💥 演示故障注入:");
        println!("================================");

        let fault_injector = self.service.get_fault_injector();

        // 网络延迟故障
        println!("注入网络延迟故障...");
        fault_injector
            .inject_network_latency("user_service", 500)
            .await?;

        // 服务不可用故障
        println!("\n注入服务不可用故障...");
        fault_injector
            .inject_service_unavailable("order_service", 10)
            .await?;

        // 资源耗尽故障
        println!("\n注入资源耗尽故障...");
        fault_injector
            .inject_resource_exhaustion("payment_service", "memory")
            .await?;

        // 依赖故障
        println!("\n注入依赖故障...");
        fault_injector
            .inject_dependency_failure("notification_service", "email_service")
            .await?;

        // 数据损坏故障
        println!("\n注入数据损坏故障...");
        fault_injector
            .inject_data_corruption("database_service", "user_data")
            .await?;

        // 获取活跃故障
        let active_faults = fault_injector.get_active_faults().await;
        println!("\n当前活跃故障数: {}", active_faults.len());

        // 获取混沌指标
        let metrics = fault_injector.get_metrics().await;
        println!("\n混沌指标:");
        println!("  - 总实验数: {}", metrics.total_experiments);
        println!("  - 成功实验数: {}", metrics.successful_experiments);
        println!("  - 失败实验数: {}", metrics.failed_experiments);
        println!("  - 总注入故障数: {}", metrics.total_faults_injected);
        println!("  - 平均恢复时间: {:.2}秒", metrics.average_recovery_time);
        println!("  - 系统正常运行时间: {:.2}%", metrics.system_uptime);

        Ok(())
    }

    /// 演示混沌实验
    pub async fn demo_chaos_experiments(&self) -> Result<()> {
        println!("\n🧪 演示混沌实验:");
        println!("================================");

        let chaos_monkey = self.service.get_chaos_monkey();

        // 创建混沌实验
        let experiments = vec![
            ChaosExperiment {
                id: "network_latency_exp".to_string(),
                name: "网络延迟实验".to_string(),
                description: "测试系统对网络延迟的响应".to_string(),
                fault_type: FaultType::NetworkLatency,
                severity: Severity::Medium,
                target_services: vec!["user_service".to_string(), "order_service".to_string()],
                parameters: HashMap::from([("delay_ms".to_string(), "1000".to_string())]),
                duration: 60,
                start_time: None,
                end_time: None,
                status: ExperimentStatus::Planned,
                results: None,
            },
            ChaosExperiment {
                id: "service_unavailable_exp".to_string(),
                name: "服务不可用实验".to_string(),
                description: "测试系统对服务不可用的响应".to_string(),
                fault_type: FaultType::ServiceUnavailable,
                severity: Severity::High,
                target_services: vec!["payment_service".to_string()],
                parameters: HashMap::from([("duration_sec".to_string(), "30".to_string())]),
                duration: 60,
                start_time: None,
                end_time: None,
                status: ExperimentStatus::Planned,
                results: None,
            },
            ChaosExperiment {
                id: "resource_exhaustion_exp".to_string(),
                name: "资源耗尽实验".to_string(),
                description: "测试系统对资源耗尽的响应".to_string(),
                fault_type: FaultType::ResourceExhaustion,
                severity: Severity::Critical,
                target_services: vec!["database_service".to_string()],
                parameters: HashMap::from([("resource_type".to_string(), "memory".to_string())]),
                duration: 60,
                start_time: None,
                end_time: None,
                status: ExperimentStatus::Planned,
                results: None,
            },
        ];

        // 创建实验
        for experiment in experiments {
            let experiment_id = chaos_monkey.create_experiment(experiment).await?;
            println!("✅ 创建实验: {}", experiment_id);
        }

        // 运行实验
        let experiment_ids = vec![
            "network_latency_exp",
            "service_unavailable_exp",
            "resource_exhaustion_exp",
        ];

        for experiment_id in experiment_ids {
            println!("\n运行实验: {}", experiment_id);
            let results = chaos_monkey.run_experiment(experiment_id).await?;

            println!("实验结果:");
            println!("  - 总请求数: {}", results.total_requests);
            println!("  - 成功请求数: {}", results.successful_requests);
            println!("  - 失败请求数: {}", results.failed_requests);
            println!("  - 平均响应时间: {:.2}ms", results.average_response_time);
            println!("  - 最大响应时间: {:.2}ms", results.max_response_time);
            println!("  - 最小响应时间: {:.2}ms", results.min_response_time);
            println!("  - 系统稳定性: {:?}", results.system_stability);
            println!("  - 建议:");
            for recommendation in &results.recommendations {
                println!("    * {}", recommendation);
            }
        }

        // 获取所有实验
        let all_experiments = chaos_monkey.get_experiments().await;
        println!("\n所有实验:");
        for experiment in all_experiments {
            println!(
                "  - {} ({:?}) - 状态: {:?}",
                experiment.name, experiment.fault_type, experiment.status
            );
        }

        Ok(())
    }

    /// 演示混沌猴子
    pub async fn demo_chaos_monkey(&self) -> Result<()> {
        println!("\n🐒 演示混沌猴子:");
        println!("================================");

        let chaos_monkey = self.service.get_chaos_monkey();

        // 启动混沌猴子
        println!("启动混沌猴子...");
        chaos_monkey.start().await?;

        // 让混沌猴子运行一段时间
        println!("混沌猴子运行中，观察故障注入...");
        sleep(Duration::from_secs(30)).await;

        // 停止混沌猴子
        println!("停止混沌猴子...");
        chaos_monkey.stop().await?;

        // 获取混沌指标
        let metrics = self.service.get_chaos_metrics().await;
        println!("\n混沌猴子运行结果:");
        println!("  - 总实验数: {}", metrics.total_experiments);
        println!("  - 成功实验数: {}", metrics.successful_experiments);
        println!("  - 失败实验数: {}", metrics.failed_experiments);
        println!("  - 总注入故障数: {}", metrics.total_faults_injected);
        println!("  - 平均恢复时间: {:.2}秒", metrics.average_recovery_time);
        println!("  - 系统正常运行时间: {:.2}%", metrics.system_uptime);

        Ok(())
    }

    /// 演示弹性测试
    pub async fn demo_resilience_testing(&self) -> Result<()> {
        println!("\n🛡️  演示弹性测试:");
        println!("================================");

        let resilience_tester = self.service.get_resilience_tester();

        // 运行弹性测试
        let test_results = resilience_tester
            .run_resilience_test("系统弹性测试", 60)
            .await?;

        println!("弹性测试结果:");
        println!("  - 测试名称: {}", test_results.test_name);
        println!("  - 测试时长: {} 秒", test_results.duration_sec);
        println!("  - 总实验数: {}", test_results.total_experiments);
        println!("  - 总请求数: {}", test_results.total_requests);
        println!("  - 成功请求数: {}", test_results.successful_requests);
        println!("  - 失败请求数: {}", test_results.failed_requests);
        println!("  - 成功率: {:.2}%", test_results.success_rate * 100.0);
        println!(
            "  - 平均响应时间: {:.2}ms",
            test_results.average_response_time
        );
        println!("  - 系统稳定性: {:?}", test_results.system_stability);
        println!("  - 建议:");
        for recommendation in &test_results.recommendations {
            println!("    * {}", recommendation);
        }

        Ok(())
    }

    /// 演示混沌工程配置
    pub async fn demo_chaos_configuration(&self) -> Result<()> {
        println!("\n⚙️  演示混沌工程配置:");
        println!("================================");

        let config = self.service.get_config();

        println!("当前混沌工程配置:");
        println!(
            "  - 混沌猴子: {}",
            if config.enable_chaos_monkey {
                "启用"
            } else {
                "禁用"
            }
        );
        println!("  - 故障率: {:.1}%", config.failure_rate * 100.0);
        println!("  - 实验持续时间: {} 秒", config.experiment_duration);
        println!("  - 恢复超时: {} 秒", config.recovery_timeout);
        println!("  - 最大并发实验数: {}", config.max_concurrent_experiments);
        println!(
            "  - 自动恢复: {}",
            if config.enable_auto_recovery {
                "启用"
            } else {
                "禁用"
            }
        );
        println!(
            "  - 监控: {}",
            if config.monitoring_enabled {
                "启用"
            } else {
                "禁用"
            }
        );

        println!("\n配置建议:");
        if config.failure_rate > 0.2 {
            println!("  ⚠️  故障率较高，可能影响系统稳定性");
        }
        if config.max_concurrent_experiments > 5 {
            println!("  ⚠️  并发实验数较多，可能影响系统性能");
        }
        if !config.enable_auto_recovery {
            println!("  ⚠️  建议启用自动恢复以提高系统弹性");
        }
        if !config.monitoring_enabled {
            println!("  ⚠️  建议启用监控以便观察实验效果");
        }

        Ok(())
    }

    /// 演示混沌工程最佳实践
    pub async fn demo_chaos_engineering_best_practices(&self) -> Result<()> {
        println!("\n📚 演示混沌工程最佳实践:");
        println!("================================");

        println!("混沌工程最佳实践:");
        println!();

        println!("🎯 实验设计:");
        println!("  ✅ 从小规模实验开始");
        println!("  ✅ 在非生产环境进行实验");
        println!("  ✅ 设置明确的实验目标");
        println!("  ✅ 定义成功和失败的标准");
        println!("  ✅ 准备回滚计划");
        println!();

        println!("🛡️  安全措施:");
        println!("  ✅ 设置故障率限制");
        println!("  ✅ 实施监控和告警");
        println!("  ✅ 准备自动恢复机制");
        println!("  ✅ 设置实验时间限制");
        println!("  ✅ 避免影响关键业务");
        println!();

        println!("📊 监控和度量:");
        println!("  ✅ 监控系统性能指标");
        println!("  ✅ 记录实验过程和结果");
        println!("  ✅ 分析系统行为变化");
        println!("  ✅ 跟踪恢复时间");
        println!("  ✅ 评估系统弹性");
        println!();

        println!("🔄 持续改进:");
        println!("  ✅ 定期进行混沌实验");
        println!("  ✅ 根据实验结果优化系统");
        println!("  ✅ 更新故障恢复策略");
        println!("  ✅ 分享经验和教训");
        println!("  ✅ 建立混沌工程文化");
        println!();

        println!("🚨 注意事项:");
        println!("  ⚠️  避免在生产环境进行高风险实验");
        println!("  ⚠️  确保有足够的监控和告警");
        println!("  ⚠️  准备快速回滚和恢复机制");
        println!("  ⚠️  与团队充分沟通实验计划");
        println!("  ⚠️  记录所有实验和结果");

        Ok(())
    }

    /// 演示故障类型和严重程度
    pub async fn demo_fault_types_and_severity(&self) -> Result<()> {
        println!("\n🔍 演示故障类型和严重程度:");
        println!("================================");

        println!("故障类型:");
        println!("  🌐 网络延迟 (NetworkLatency)");
        println!("    - 影响: 响应时间增加");
        println!("    - 恢复: 自动恢复");
        println!("    - 建议: 增加超时和重试机制");
        println!();

        println!("  🚫 服务不可用 (ServiceUnavailable)");
        println!("    - 影响: 服务完全不可访问");
        println!("    - 恢复: 需要手动或自动重启");
        println!("    - 建议: 实现服务降级和熔断器");
        println!();

        println!("  💾 资源耗尽 (ResourceExhaustion)");
        println!("    - 影响: 内存、CPU、磁盘等资源不足");
        println!("    - 恢复: 释放资源或扩容");
        println!("    - 建议: 实现资源监控和自动扩容");
        println!();

        println!("  🔗 依赖故障 (DependencyFailure)");
        println!("    - 影响: 依赖服务不可用");
        println!("    - 恢复: 依赖服务恢复");
        println!("    - 建议: 实现熔断器和降级机制");
        println!();

        println!("  💥 数据损坏 (DataCorruption)");
        println!("    - 影响: 数据不一致或丢失");
        println!("    - 恢复: 数据修复或恢复");
        println!("    - 建议: 实现数据备份和校验");
        println!();

        println!("故障严重程度:");
        println!("  🟢 低 (Low)");
        println!("    - 影响范围: 单个功能");
        println!("    - 用户体验: 轻微影响");
        println!("    - 恢复时间: < 5 分钟");
        println!();

        println!("  🟡 中 (Medium)");
        println!("    - 影响范围: 多个功能");
        println!("    - 用户体验: 明显影响");
        println!("    - 恢复时间: 5-30 分钟");
        println!();

        println!("  🟠 高 (High)");
        println!("    - 影响范围: 整个服务");
        println!("    - 用户体验: 严重影响");
        println!("    - 恢复时间: 30 分钟 - 2 小时");
        println!();

        println!("  🔴 严重 (Critical)");
        println!("    - 影响范围: 整个系统");
        println!("    - 用户体验: 完全不可用");
        println!("    - 恢复时间: > 2 小时");

        Ok(())
    }
}

impl Default for ChaosEngineeringDemoManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 主函数演示混沌工程
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 混沌工程演示");
    println!("================================");

    // 创建混沌工程演示管理器
    let demo_manager = ChaosEngineeringDemoManager::new();

    // 演示故障注入
    demo_manager.demo_fault_injection().await?;

    // 演示混沌实验
    demo_manager.demo_chaos_experiments().await?;

    // 演示混沌猴子
    demo_manager.demo_chaos_monkey().await?;

    // 演示弹性测试
    demo_manager.demo_resilience_testing().await?;

    // 演示故障类型和严重程度
    demo_manager.demo_fault_types_and_severity().await?;

    // 演示混沌工程配置
    demo_manager.demo_chaos_configuration().await?;

    // 演示混沌工程最佳实践
    demo_manager.demo_chaos_engineering_best_practices().await?;

    println!("\n✅ 混沌工程演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 故障注入: 模拟各种故障场景");
    println!("- 混沌实验: 系统化的故障测试");
    println!("- 混沌猴子: 自动化的故障注入");
    println!("- 弹性测试: 系统弹性评估");
    println!("- 监控指标: 完整的性能监控");
    println!("- 自动恢复: 智能的故障恢复");
    println!();
    println!("📚 混沌工程价值:");
    println!("- 提高系统可靠性");
    println!("- 验证故障恢复能力");
    println!("- 发现系统薄弱环节");
    println!("- 建立故障处理经验");
    println!("- 提升团队应急能力");
    println!("- 增强系统弹性");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_chaos_demo() {
        let demo_manager = ChaosEngineeringDemoManager::new();
        let result = demo_manager.demo_fault_injection().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_chaos_experiments() {
        let demo_manager = ChaosEngineeringDemoManager::new();
        let result = demo_manager.demo_chaos_experiments().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_resilience_testing() {
        let demo_manager = ChaosEngineeringDemoManager::new();
        let result = demo_manager.demo_resilience_testing().await;
        assert!(result.is_ok());
    }
}
