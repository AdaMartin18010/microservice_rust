//! 自动扩缩容演示
//!
//! 本示例展示了智能自动扩缩容功能：
//! - 水平扩缩容 (Horizontal Pod Autoscaling)
//! - 垂直扩缩容 (Vertical Pod Autoscaling)
//! - 预测性扩缩容 (Predictive Autoscaling)
//! - 自定义指标扩缩容 (Custom Metrics Autoscaling)

use anyhow::Result;
use std::collections::HashMap;
use tokio::time::{Duration, sleep};

// 导入我们的自动扩缩容模块
use microservice::auto_scaling::*;

/// 自动扩缩容演示管理器
pub struct AutoScalingDemoManager {
    service: AutoScalingService,
}

impl AutoScalingDemoManager {
    pub fn new() -> Self {
        let config = ScalingConfig {
            enable_horizontal_scaling: true,
            enable_vertical_scaling: true,
            enable_predictive_scaling: true,
            min_replicas: 1,
            max_replicas: 5,
            target_cpu_utilization: 70.0,
            target_memory_utilization: 80.0,
            scale_up_threshold: 80.0,
            scale_down_threshold: 30.0,
            scale_up_cooldown: 60,    // 1 minute
            scale_down_cooldown: 120, // 2 minutes
            predictive_window: 1800,  // 30 minutes
            custom_metrics: vec![
                CustomMetric {
                    name: "response_time".to_string(),
                    metric_type: MetricType::ResponseTime,
                    target_value: 200.0,
                    weight: 0.3,
                    enabled: true,
                },
                CustomMetric {
                    name: "error_rate".to_string(),
                    metric_type: MetricType::ErrorRate,
                    target_value: 5.0,
                    weight: 0.2,
                    enabled: true,
                },
            ],
        };

        let service = AutoScalingServiceFactory::create_custom_service(config);
        Self { service }
    }

    /// 演示水平扩缩容
    pub async fn demo_horizontal_scaling(&self) -> Result<()> {
        println!("\n📊 演示水平扩缩容:");
        println!("================================");

        // 获取水平扩缩容器
        let horizontal_scaler = self.service.horizontal_scaler();

        // 模拟高负载场景
        println!("模拟高负载场景...");
        let high_load_metrics = ResourceMetrics {
            timestamp: chrono::Utc::now(),
            cpu_usage: 90.0,
            memory_usage: 85.0,
            request_rate: 1500.0,
            response_time: 800.0,
            error_rate: 2.0,
            active_connections: 500,
            queue_length: 50,
            custom_metrics: HashMap::new(),
        };

        let action = horizontal_scaler
            .evaluate_scaling(&high_load_metrics)
            .await?;
        println!("高负载评估结果: {:?}", action);

        if action != ScalingAction::NoAction {
            let scaling_event = horizontal_scaler
                .execute_scaling(action, &high_load_metrics)
                .await?;
            println!(
                "扩缩容事件: {} -> {} (原因: {})",
                scaling_event.current_replicas, scaling_event.target_replicas, scaling_event.reason
            );
        }

        // 模拟低负载场景
        println!("\n模拟低负载场景...");
        let low_load_metrics = ResourceMetrics {
            timestamp: chrono::Utc::now(),
            cpu_usage: 20.0,
            memory_usage: 30.0,
            request_rate: 100.0,
            response_time: 50.0,
            error_rate: 0.5,
            active_connections: 50,
            queue_length: 5,
            custom_metrics: HashMap::new(),
        };

        let action = horizontal_scaler
            .evaluate_scaling(&low_load_metrics)
            .await?;
        println!("低负载评估结果: {:?}", action);

        if action != ScalingAction::NoAction {
            let scaling_event = horizontal_scaler
                .execute_scaling(action, &low_load_metrics)
                .await?;
            println!(
                "扩缩容事件: {} -> {} (原因: {})",
                scaling_event.current_replicas, scaling_event.target_replicas, scaling_event.reason
            );
        }

        // 显示当前状态
        let current_replicas = horizontal_scaler.get_current_replicas().await;
        println!("\n当前副本数: {}", current_replicas);

        // 显示扩缩容历史
        let scaling_history = horizontal_scaler.get_scaling_history().await;
        println!("扩缩容历史 (最近{}条):", scaling_history.len());
        for (i, event) in scaling_history.iter().rev().take(5).enumerate() {
            println!(
                "  {}. {} -> {} ({})",
                i + 1,
                event.current_replicas,
                event.target_replicas,
                event.reason
            );
        }

        Ok(())
    }

    /// 演示垂直扩缩容
    pub async fn demo_vertical_scaling(&self) -> Result<()> {
        println!("\n📈 演示垂直扩缩容:");
        println!("================================");

        // 获取垂直扩缩容器
        let vertical_scaler = self.service.vertical_scaler();

        // 模拟资源压力场景
        println!("模拟资源压力场景...");
        let high_resource_metrics = ResourceMetrics {
            timestamp: chrono::Utc::now(),
            cpu_usage: 95.0,
            memory_usage: 90.0,
            request_rate: 2000.0,
            response_time: 1200.0,
            error_rate: 3.0,
            active_connections: 800,
            queue_length: 100,
            custom_metrics: HashMap::new(),
        };

        let action = vertical_scaler
            .evaluate_scaling(&high_resource_metrics)
            .await?;
        println!("高资源使用评估结果: {:?}", action);

        if action != ScalingAction::NoAction {
            let scaling_event = vertical_scaler
                .execute_scaling(action, &high_resource_metrics)
                .await?;
            println!(
                "垂直扩缩容事件: {} (原因: {})",
                scaling_event.action, scaling_event.reason
            );
        }

        // 模拟资源充足场景
        println!("\n模拟资源充足场景...");
        let low_resource_metrics = ResourceMetrics {
            timestamp: chrono::Utc::now(),
            cpu_usage: 25.0,
            memory_usage: 35.0,
            request_rate: 200.0,
            response_time: 80.0,
            error_rate: 0.8,
            active_connections: 100,
            queue_length: 10,
            custom_metrics: HashMap::new(),
        };

        let action = vertical_scaler
            .evaluate_scaling(&low_resource_metrics)
            .await?;
        println!("低资源使用评估结果: {:?}", action);

        if action != ScalingAction::NoAction {
            let scaling_event = vertical_scaler
                .execute_scaling(action, &low_resource_metrics)
                .await?;
            println!(
                "垂直扩缩容事件: {} (原因: {})",
                scaling_event.action, scaling_event.reason
            );
        }

        // 显示当前资源限制
        let (cpu_limit, memory_limit) = vertical_scaler.get_current_limits().await;
        println!("\n当前资源限制:");
        println!("  - CPU: {:.0}m", cpu_limit);
        println!("  - Memory: {:.0}Mi", memory_limit);

        // 显示扩缩容历史
        let scaling_history = vertical_scaler.get_scaling_history().await;
        println!("垂直扩缩容历史 (最近{}条):", scaling_history.len());
        for (i, event) in scaling_history.iter().rev().take(5).enumerate() {
            println!("  {}. {} (原因: {})", i + 1, event.action, event.reason);
        }

        Ok(())
    }

    /// 演示预测性扩缩容
    pub async fn demo_predictive_scaling(&self) -> Result<()> {
        println!("\n🔮 演示预测性扩缩容:");
        println!("================================");

        // 获取预测性扩缩容器
        let predictive_scaler = self.service.predictive_scaler();

        // 生成历史指标数据
        println!("生成历史指标数据...");
        let mut metrics_history = Vec::new();
        for i in 0..30 {
            let timestamp = chrono::Utc::now() - chrono::Duration::minutes(i as i64);
            let cpu_usage = 50.0 + (i as f64 * 2.0) + (i as f64 * 0.5).sin() * 10.0;
            let memory_usage = 60.0 + (i as f64 * 1.5) + (i as f64 * 0.3).cos() * 8.0;
            let request_rate = 400.0 + (i as f64 * 15.0) + (i as f64 * 0.4).sin() * 50.0;

            metrics_history.push(ResourceMetrics {
                timestamp,
                cpu_usage: cpu_usage.min(100.0),
                memory_usage: memory_usage.min(100.0),
                request_rate,
                response_time: 100.0 + (i as f64 * 5.0),
                error_rate: 1.0 + (i as f64 * 0.1),
                active_connections: 100 + (i as u32 * 5),
                queue_length: (i as u32 * 2).min(50),
                custom_metrics: HashMap::new(),
            });
        }

        // 生成预测
        println!("生成预测数据...");
        let predictions = predictive_scaler
            .generate_predictions(&metrics_history)
            .await?;
        println!("生成了 {} 个预测数据点", predictions.len());

        for (i, prediction) in predictions.iter().enumerate() {
            println!(
                "  预测 {}: CPU {:.1}%, Memory {:.1}%, 置信度 {:.1}%",
                i + 1,
                prediction.predicted_cpu,
                prediction.predicted_memory,
                prediction.confidence * 100.0
            );
        }

        // 基于预测评估扩缩容
        let action = predictive_scaler
            .evaluate_predictive_scaling(&predictions)
            .await?;
        println!("\n预测性扩缩容评估结果: {:?}", action);

        if action != ScalingAction::NoAction {
            let scaling_event = predictive_scaler
                .execute_predictive_scaling(action, &predictions)
                .await?;
            println!(
                "预测性扩缩容事件: {} (原因: {})",
                scaling_event.action, scaling_event.reason
            );
        }

        // 训练模型
        println!("\n训练预测模型...");
        predictive_scaler.train_model(&metrics_history).await?;

        // 显示预测历史
        let prediction_history = predictive_scaler.get_prediction_history().await;
        println!("预测历史 (最近{}条):", prediction_history.len());
        for (i, prediction) in prediction_history.iter().rev().take(5).enumerate() {
            println!(
                "  {}. CPU: {:.1}%, Memory: {:.1}%, 置信度: {:.1}%",
                i + 1,
                prediction.predicted_cpu,
                prediction.predicted_memory,
                prediction.confidence * 100.0
            );
        }

        Ok(())
    }

    /// 演示自动扩缩容服务
    pub async fn demo_auto_scaling_service(&self) -> Result<()> {
        println!("\n🚀 演示自动扩缩容服务:");
        println!("================================");

        // 启动服务
        println!("启动自动扩缩容服务...");
        self.service.start().await?;

        // 让服务运行一段时间
        println!("服务运行中，观察自动扩缩容...");
        sleep(Duration::from_secs(60)).await;

        // 停止服务
        println!("停止自动扩缩容服务...");
        self.service.stop().await?;

        // 获取统计信息
        let stats = self.service.get_scaling_stats().await?;
        println!("\n扩缩容统计:");
        println!("  - 总扩缩容事件: {}", stats.total_scaling_events);
        println!("  - 扩容事件: {}", stats.scale_up_events);
        println!("  - 缩容事件: {}", stats.scale_down_events);
        println!("  - 当前副本数: {}", stats.current_replicas);
        println!("  - 当前CPU限制: {:.0}m", stats.cpu_limit);
        println!("  - 当前内存限制: {:.0}Mi", stats.memory_limit);
        println!("  - 水平扩缩容事件: {}", stats.horizontal_scaling_events);
        println!("  - 垂直扩缩容事件: {}", stats.vertical_scaling_events);
        println!("  - 预测性扩缩容事件: {}", stats.predictive_scaling_events);

        Ok(())
    }

    /// 演示扩缩容配置
    pub async fn demo_scaling_configuration(&self) -> Result<()> {
        println!("\n⚙️  演示扩缩容配置:");
        println!("================================");

        let config = self.service.get_config();

        println!("当前扩缩容配置:");
        println!(
            "  - 水平扩缩容: {}",
            if config.enable_horizontal_scaling {
                "启用"
            } else {
                "禁用"
            }
        );
        println!(
            "  - 垂直扩缩容: {}",
            if config.enable_vertical_scaling {
                "启用"
            } else {
                "禁用"
            }
        );
        println!(
            "  - 预测性扩缩容: {}",
            if config.enable_predictive_scaling {
                "启用"
            } else {
                "禁用"
            }
        );
        println!("  - 最小副本数: {}", config.min_replicas);
        println!("  - 最大副本数: {}", config.max_replicas);
        println!("  - 目标CPU使用率: {:.1}%", config.target_cpu_utilization);
        println!(
            "  - 目标内存使用率: {:.1}%",
            config.target_memory_utilization
        );
        println!("  - 扩容阈值: {:.1}%", config.scale_up_threshold);
        println!("  - 缩容阈值: {:.1}%", config.scale_down_threshold);
        println!("  - 扩容冷却时间: {} 秒", config.scale_up_cooldown);
        println!("  - 缩容冷却时间: {} 秒", config.scale_down_cooldown);
        println!("  - 预测窗口: {} 秒", config.predictive_window);
        println!("  - 自定义指标数: {}", config.custom_metrics.len());

        println!("\n自定义指标:");
        for (i, metric) in config.custom_metrics.iter().enumerate() {
            println!(
                "  {}. {} - 类型: {:?}, 目标值: {:.1}, 权重: {:.1}",
                i + 1,
                metric.name,
                metric.metric_type,
                metric.target_value,
                metric.weight
            );
        }

        println!("\n配置建议:");
        if config.scale_up_threshold > 90.0 {
            println!("  ⚠️  扩容阈值较高，可能导致响应时间增加");
        }
        if config.scale_down_threshold < 20.0 {
            println!("  ⚠️  缩容阈值较低，可能导致频繁扩缩容");
        }
        if config.scale_up_cooldown < 60 {
            println!("  ⚠️  扩容冷却时间较短，可能导致过度扩容");
        }
        if config.scale_down_cooldown < 120 {
            println!("  ⚠️  缩容冷却时间较短，可能导致频繁缩容");
        }

        Ok(())
    }

    /// 演示扩缩容最佳实践
    pub async fn demo_scaling_best_practices(&self) -> Result<()> {
        println!("\n📚 演示扩缩容最佳实践:");
        println!("================================");

        println!("自动扩缩容最佳实践:");
        println!();

        println!("🎯 扩缩容策略:");
        println!("  ✅ 设置合理的扩缩容阈值");
        println!("  ✅ 配置适当的冷却时间");
        println!("  ✅ 使用多个指标进行决策");
        println!("  ✅ 实施渐进式扩缩容");
        println!("  ✅ 设置扩缩容边界");
        println!();

        println!("📊 监控和指标:");
        println!("  ✅ 监控CPU、内存、网络等基础指标");
        println!("  ✅ 监控应用级指标（响应时间、错误率）");
        println!("  ✅ 监控业务指标（请求量、用户数）");
        println!("  ✅ 设置告警和通知");
        println!("  ✅ 定期分析扩缩容效果");
        println!();

        println!("🔄 水平扩缩容:");
        println!("  ✅ 优先使用水平扩缩容");
        println!("  ✅ 确保应用无状态");
        println!("  ✅ 实现健康检查");
        println!("  ✅ 配置负载均衡");
        println!("  ✅ 设置合理的副本数范围");
        println!();

        println!("📈 垂直扩缩容:");
        println!("  ✅ 谨慎使用垂直扩缩容");
        println!("  ✅ 考虑容器重启影响");
        println!("  ✅ 设置资源限制范围");
        println!("  ✅ 监控资源使用趋势");
        println!("  ✅ 结合水平扩缩容使用");
        println!();

        println!("🔮 预测性扩缩容:");
        println!("  ✅ 收集足够的历史数据");
        println!("  ✅ 训练准确的预测模型");
        println!("  ✅ 考虑业务周期性");
        println!("  ✅ 设置预测置信度阈值");
        println!("  ✅ 结合实时指标验证");
        println!();

        println!("🛡️  稳定性保障:");
        println!("  ✅ 设置扩缩容冷却时间");
        println!("  ✅ 实施扩缩容速率限制");
        println!("  ✅ 配置扩缩容失败重试");
        println!("  ✅ 实现扩缩容回滚机制");
        println!("  ✅ 监控扩缩容事件");

        Ok(())
    }

    /// 演示扩缩容类型比较
    pub async fn demo_scaling_types_comparison(&self) -> Result<()> {
        println!("\n📊 演示扩缩容类型比较:");
        println!("================================");

        println!("扩缩容类型比较:");
        println!();

        println!("🔄 水平扩缩容 (HPA):");
        println!("  ✅ 优点:");
        println!("    - 提高系统可用性");
        println!("    - 更好的故障隔离");
        println!("    - 支持负载分布");
        println!("    - 易于实现");
        println!("  ❌ 缺点:");
        println!("    - 需要应用无状态");
        println!("    - 可能增加资源消耗");
        println!("    - 需要负载均衡");
        println!("    - 扩缩容需要时间");
        println!();

        println!("📈 垂直扩缩容 (VPA):");
        println!("  ✅ 优点:");
        println!("    - 提高资源利用率");
        println!("    - 减少资源浪费");
        println!("    - 适合有状态应用");
        println!("    - 响应速度快");
        println!("  ❌ 缺点:");
        println!("    - 需要重启容器");
        println!("    - 单点故障风险");
        println!("    - 扩缩容范围有限");
        println!("    - 实现复杂度高");
        println!();

        println!("🔮 预测性扩缩容:");
        println!("  ✅ 优点:");
        println!("    - 提前应对负载变化");
        println!("    - 减少响应延迟");
        println!("    - 优化资源使用");
        println!("    - 提高用户体验");
        println!("  ❌ 缺点:");
        println!("    - 需要历史数据");
        println!("    - 预测可能不准确");
        println!("    - 实现复杂度高");
        println!("    - 需要持续调优");
        println!();

        println!("🎯 选择建议:");
        println!("  - 优先使用水平扩缩容");
        println!("  - 谨慎使用垂直扩缩容");
        println!("  - 结合预测性扩缩容");
        println!("  - 根据应用特性选择");
        println!("  - 定期评估和优化");

        Ok(())
    }
}

impl Default for AutoScalingDemoManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 主函数演示自动扩缩容
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 自动扩缩容演示");
    println!("================================");

    // 创建自动扩缩容演示管理器
    let demo_manager = AutoScalingDemoManager::new();

    // 演示水平扩缩容
    demo_manager.demo_horizontal_scaling().await?;

    // 演示垂直扩缩容
    demo_manager.demo_vertical_scaling().await?;

    // 演示预测性扩缩容
    demo_manager.demo_predictive_scaling().await?;

    // 演示扩缩容类型比较
    demo_manager.demo_scaling_types_comparison().await?;

    // 演示扩缩容配置
    demo_manager.demo_scaling_configuration().await?;

    // 演示自动扩缩容服务
    demo_manager.demo_auto_scaling_service().await?;

    // 演示扩缩容最佳实践
    demo_manager.demo_scaling_best_practices().await?;

    println!("\n✅ 自动扩缩容演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 水平扩缩容: 自动调整副本数量");
    println!("- 垂直扩缩容: 自动调整资源限制");
    println!("- 预测性扩缩容: 基于预测提前扩缩容");
    println!("- 自定义指标: 支持业务指标扩缩容");
    println!("- 智能策略: 多种扩缩容策略");
    println!("- 监控告警: 完整的监控体系");
    println!();
    println!("📚 扩缩容价值:");
    println!("- 提高系统可用性");
    println!("- 优化资源使用");
    println!("- 降低运维成本");
    println!("- 提升用户体验");
    println!("- 支持业务增长");
    println!("- 增强系统弹性");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_horizontal_scaling() {
        let demo_manager = AutoScalingDemoManager::new();
        let result = demo_manager.demo_horizontal_scaling().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_vertical_scaling() {
        let demo_manager = AutoScalingDemoManager::new();
        let result = demo_manager.demo_vertical_scaling().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_predictive_scaling() {
        let demo_manager = AutoScalingDemoManager::new();
        let result = demo_manager.demo_predictive_scaling().await;
        assert!(result.is_ok());
    }
}
