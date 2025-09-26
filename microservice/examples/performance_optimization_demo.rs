//! 性能优化演示
//!
//! 本示例展示了全面的性能优化功能：
//! - 基准测试 (Benchmark Testing)
//! - 内存优化 (Memory Optimization)
//! - 并发优化 (Concurrency Optimization)
//! - 性能监控 (Performance Monitoring)
//! - 性能分析 (Performance Profiling)
//! - 优化建议 (Optimization Recommendations)

use anyhow::Result;
use std::collections::HashMap;
use tokio::time::{Duration, sleep};

// 导入我们的性能优化模块
use microservice::performance_optimization::*;

/// 性能优化演示管理器
pub struct PerformanceOptimizationDemoManager {
    manager: PerformanceOptimizationManager,
}

impl PerformanceOptimizationDemoManager {
    pub fn new() -> Self {
        let mut manager = PerformanceOptimizationFactory::create_optimization_manager();

        // 设置基准测试器
        let benchmark_config = PerformanceOptimizationFactory::create_default_benchmark_config();
        manager.set_benchmarker(benchmark_config);

        // 设置内存优化器
        let memory_config = PerformanceOptimizationFactory::create_default_memory_config();
        manager.set_memory_optimizer(memory_config);

        // 设置并发优化器
        let concurrency_config =
            PerformanceOptimizationFactory::create_default_concurrency_config();
        manager.set_concurrency_optimizer(concurrency_config);

        Self { manager }
    }

    /// 演示基准测试
    pub async fn demo_benchmark_testing(&self) -> Result<()> {
        println!("\n📊 演示基准测试:");
        println!("================================");

        // 创建自定义基准测试配置
        let benchmark_config = BenchmarkConfig {
            name: "微服务性能基准测试".to_string(),
            description: "测试微服务的响应时间和吞吐量".to_string(),
            duration_seconds: 30,
            concurrency_level: 20,
            warmup_seconds: 5,
            ramp_up_seconds: 3,
            ramp_down_seconds: 2,
            target_throughput: Some(2000.0),
            target_response_time: Some(50.0),
            max_error_rate: Some(0.5),
            custom_parameters: HashMap::from([
                ("test_type".to_string(), "microservice".to_string()),
                ("environment".to_string(), "demo".to_string()),
            ]),
        };

        let benchmarker = PerformanceBenchmarker::new(benchmark_config);

        // 定义测试函数
        let test_function = || async {
            // 模拟微服务请求处理
            sleep(Duration::from_millis(10)).await;

            // 模拟一些计算
            let _ = (0..1000).fold(0, |acc, x| acc + x);

            // 模拟偶尔的错误
            if rand::random::<f64>() < 0.01 {
                return Err(anyhow::anyhow!("模拟错误"));
            }

            Ok(())
        };

        // 运行基准测试
        let result = benchmarker.run_benchmark(test_function).await?;

        // 分析结果
        self.analyze_benchmark_results(&result).await?;

        Ok(())
    }

    /// 分析基准测试结果
    async fn analyze_benchmark_results(&self, result: &BenchmarkResult) -> Result<()> {
        println!("\n📈 基准测试结果分析:");
        println!("================================");

        // 性能评级
        let performance_grade = self.calculate_performance_grade(result);
        println!("性能评级: {}", performance_grade);

        // 瓶颈分析
        let bottlenecks = self.identify_performance_bottlenecks(result);
        if !bottlenecks.is_empty() {
            println!("性能瓶颈:");
            for bottleneck in bottlenecks {
                println!("  - {}", bottleneck);
            }
        }

        // 优化建议
        let recommendations = self.generate_benchmark_recommendations(result);
        if !recommendations.is_empty() {
            println!("优化建议:");
            for recommendation in recommendations {
                println!("  - {}", recommendation);
            }
        }

        // 与目标对比
        self.compare_with_targets(result).await?;

        Ok(())
    }

    /// 计算性能评级
    fn calculate_performance_grade(&self, result: &BenchmarkResult) -> String {
        let mut score = 0;

        // 吞吐量评分
        if let Some(target) = result.config.target_throughput {
            if result.throughput_per_second >= target {
                score += 25;
            } else if result.throughput_per_second >= target * 0.8 {
                score += 20;
            } else if result.throughput_per_second >= target * 0.6 {
                score += 15;
            } else {
                score += 10;
            }
        }

        // 响应时间评分
        if let Some(target) = result.config.target_response_time {
            if result.average_response_time <= target {
                score += 25;
            } else if result.average_response_time <= target * 1.2 {
                score += 20;
            } else if result.average_response_time <= target * 1.5 {
                score += 15;
            } else {
                score += 10;
            }
        }

        // 错误率评分
        if let Some(target) = result.config.max_error_rate {
            if result.error_rate <= target {
                score += 25;
            } else if result.error_rate <= target * 2.0 {
                score += 20;
            } else if result.error_rate <= target * 3.0 {
                score += 15;
            } else {
                score += 10;
            }
        }

        // 稳定性评分
        let stability_score = if result.error_rate < 1.0 { 25 } else { 15 };
        score += stability_score;

        match score {
            90..=100 => "A+ (优秀)".to_string(),
            80..=89 => "A (良好)".to_string(),
            70..=79 => "B+ (中等)".to_string(),
            60..=69 => "B (及格)".to_string(),
            50..=59 => "C (需要改进)".to_string(),
            _ => "D (不合格)".to_string(),
        }
    }

    /// 识别性能瓶颈
    fn identify_performance_bottlenecks(&self, result: &BenchmarkResult) -> Vec<String> {
        let mut bottlenecks = Vec::new();

        if result.p99_response_time > result.average_response_time * 5.0 {
            bottlenecks.push("响应时间分布不均匀，存在长尾延迟".to_string());
        }

        if result.error_rate > 1.0 {
            bottlenecks.push("错误率过高，影响系统稳定性".to_string());
        }

        if result.memory_usage_mb > 1000.0 {
            bottlenecks.push("内存使用过高，可能存在内存泄漏".to_string());
        }

        if result.cpu_usage_percent > 90.0 {
            bottlenecks.push("CPU使用率过高，可能成为性能瓶颈".to_string());
        }

        if result.throughput_per_second < 100.0 {
            bottlenecks.push("吞吐量较低，需要优化处理逻辑".to_string());
        }

        bottlenecks
    }

    /// 生成基准测试建议
    #[allow(unused_variables)]
    fn generate_benchmark_recommendations(&self, result: &BenchmarkResult) -> Vec<String> {
        let recommendations: Vec<String> = vec![
            "减少内存分配".to_string(),
            "优化热点路径".to_string(),
            "批量 I/O".to_string(),
            "提高缓存命中率".to_string(),
            "调整并发模型".to_string(),
            "连接复用".to_string(),
            "降低日志开销".to_string(),
            "合理的超时与重试".to_string(),
            "模块解耦".to_string(),
            "监控覆盖".to_string(),
            "编译优化".to_string(),
            "线程池调优".to_string(),
            "缓存淘汰策略".to_string(),
            "零拷贝".to_string(),
        ];
        recommendations
    }

    /// 与目标对比
    async fn compare_with_targets(&self, result: &BenchmarkResult) -> Result<()> {
        println!("\n🎯 与目标对比:");
        println!("================================");

        if let Some(target_throughput) = result.config.target_throughput {
            let throughput_achievement = (result.throughput_per_second / target_throughput) * 100.0;
            println!(
                "吞吐量目标: {:.0} req/s, 实际: {:.2} req/s, 达成率: {:.1}%",
                target_throughput, result.throughput_per_second, throughput_achievement
            );
        }

        if let Some(target_response_time) = result.config.target_response_time {
            let response_time_ratio = result.average_response_time / target_response_time;
            println!(
                "响应时间目标: {:.0} ms, 实际: {:.2} ms, 比率: {:.2}x",
                target_response_time, result.average_response_time, response_time_ratio
            );
        }

        if let Some(max_error_rate) = result.config.max_error_rate {
            let error_rate_ratio = result.error_rate / max_error_rate;
            println!(
                "错误率目标: {:.1}%, 实际: {:.2}%, 比率: {:.2}x",
                max_error_rate, result.error_rate, error_rate_ratio
            );
        }

        Ok(())
    }

    /// 演示内存优化
    pub async fn demo_memory_optimization(&self) -> Result<()> {
        println!("\n🧠 演示内存优化:");
        println!("================================");

        // 创建内存优化器
        let memory_config = MemoryOptimizationConfig {
            enable_pooling: true,
            enable_compression: true,
            enable_deduplication: true,
            max_memory_usage_mb: 2048.0,
            gc_threshold_percent: 85.0,
            pool_size: 200,
            compression_level: 9,
            deduplication_window: 2000,
        };

        let memory_optimizer = MemoryOptimizer::new(memory_config);

        // 获取优化前统计
        let before_stats = memory_optimizer.get_memory_stats().await;
        println!("优化前内存统计:");
        println!("  - 总内存: {:.2} MB", before_stats.total_memory_mb);
        println!("  - 已用内存: {:.2} MB", before_stats.used_memory_mb);
        println!(
            "  - 内存碎片: {:.2}%",
            before_stats.memory_fragmentation_percent
        );

        // 运行内存优化
        let optimization_result = memory_optimizer.optimize_memory().await?;

        // 获取优化后统计
        let after_stats = memory_optimizer.get_memory_stats().await;
        println!("\n优化后内存统计:");
        println!("  - 总内存: {:.2} MB", after_stats.total_memory_mb);
        println!("  - 已用内存: {:.2} MB", after_stats.used_memory_mb);
        println!(
            "  - 内存碎片: {:.2}%",
            after_stats.memory_fragmentation_percent
        );

        // 分析优化效果
        self.analyze_memory_optimization(&optimization_result)
            .await?;

        Ok(())
    }

    /// 分析内存优化效果
    async fn analyze_memory_optimization(&self, result: &MemoryOptimizationResult) -> Result<()> {
        println!("\n📈 内存优化效果分析:");
        println!("================================");

        let memory_saved_percent =
            (result.memory_saved_mb / result.start_stats.used_memory_mb) * 100.0;
        println!(
            "内存节省: {:.2} MB ({:.1}%)",
            result.memory_saved_mb, memory_saved_percent
        );

        let fragmentation_reduction_percent = result.fragmentation_reduced_percent;
        println!("碎片减少: {:.2}%", fragmentation_reduction_percent);

        let optimization_efficiency = result.memory_saved_mb / result.optimization_time_ms * 1000.0;
        println!("优化效率: {:.2} MB/s", optimization_efficiency);

        // 优化建议
        if memory_saved_percent < 10.0 {
            println!("建议: 考虑启用更多内存优化策略");
        }

        if fragmentation_reduction_percent < 5.0 {
            println!("建议: 优化内存分配策略");
        }

        Ok(())
    }

    /// 演示并发优化
    pub async fn demo_concurrency_optimization(&self) -> Result<()> {
        println!("\n⚡ 演示并发优化:");
        println!("================================");

        // 创建并发优化器
        let concurrency_config = ConcurrencyOptimizationConfig {
            max_concurrent_requests: 2000,
            thread_pool_size: 50,
            async_task_limit: 10000,
            connection_pool_size: 200,
            batch_size: 100,
            timeout_ms: 3000,
            backpressure_threshold: 0.85,
            circuit_breaker_threshold: 0.05,
        };

        let concurrency_optimizer = ConcurrencyOptimizer::new(concurrency_config);

        // 获取优化前统计
        let before_stats = concurrency_optimizer.get_concurrency_stats().await;
        println!("优化前并发统计:");
        println!("  - 活跃连接: {}", before_stats.active_connections);
        println!("  - 活跃请求: {}", before_stats.active_requests);
        println!(
            "  - 线程池利用率: {:.1}%",
            before_stats.thread_pool_utilization
        );

        // 运行并发优化
        let optimization_result = concurrency_optimizer.optimize_concurrency().await?;

        // 获取优化后统计
        let after_stats = concurrency_optimizer.get_concurrency_stats().await;
        println!("\n优化后并发统计:");
        println!("  - 活跃连接: {}", after_stats.active_connections);
        println!("  - 活跃请求: {}", after_stats.active_requests);
        println!(
            "  - 线程池利用率: {:.1}%",
            after_stats.thread_pool_utilization
        );

        // 分析优化效果
        self.analyze_concurrency_optimization(&optimization_result)
            .await?;

        Ok(())
    }

    /// 分析并发优化效果
    async fn analyze_concurrency_optimization(
        &self,
        result: &ConcurrencyOptimizationResult,
    ) -> Result<()> {
        println!("\n📈 并发优化效果分析:");
        println!("================================");

        println!("吞吐量提升: {:.1}%", result.throughput_improvement_percent);
        println!("延迟减少: {:.1}%", result.latency_reduction_percent);
        println!("错误率减少: {:.1}%", result.error_rate_reduction_percent);

        let optimization_efficiency =
            result.throughput_improvement_percent / result.optimization_time_ms * 1000.0;
        println!("优化效率: {:.2}% 提升/秒", optimization_efficiency);

        // 性能评级
        let overall_improvement = (result.throughput_improvement_percent
            + result.latency_reduction_percent
            + result.error_rate_reduction_percent)
            / 3.0;

        let grade = match overall_improvement {
            30.0..=100.0 => "A+ (优秀)",
            20.0..=29.9 => "A (良好)",
            10.0..=19.9 => "B+ (中等)",
            5.0..=9.9 => "B (及格)",
            _ => "C (需要改进)",
        };

        println!("并发优化评级: {}", grade);

        Ok(())
    }

    /// 演示全面性能优化
    pub async fn demo_comprehensive_optimization(&self) -> Result<()> {
        println!("\n🚀 演示全面性能优化:");
        println!("================================");

        // 定义测试函数
        let test_function = || async {
            // 模拟复杂的微服务请求
            sleep(Duration::from_millis(5)).await;

            // 模拟数据处理
            let data = (0..10000).collect::<Vec<i32>>();
            let _ = data.iter().map(|x| x * 2).collect::<Vec<i32>>();

            // 模拟网络调用
            sleep(Duration::from_millis(3)).await;

            // 模拟数据库操作
            sleep(Duration::from_millis(2)).await;

            Ok(())
        };

        // 运行全面优化
        let comprehensive_result = self
            .manager
            .run_comprehensive_optimization(test_function)
            .await?;

        // 分析全面优化结果
        self.analyze_comprehensive_optimization(&comprehensive_result)
            .await?;

        Ok(())
    }

    /// 分析全面优化结果
    async fn analyze_comprehensive_optimization(
        &self,
        result: &ComprehensiveOptimizationResult,
    ) -> Result<()> {
        println!("\n📈 全面优化结果分析:");
        println!("================================");

        println!("总改进: {:.1}%", result.total_improvement_percent);
        println!("优化时长: {:.2} ms", result.optimization_duration_ms);

        // 分析各类优化结果
        for optimization_result in &result.results {
            match optimization_result {
                OptimizationResult::Benchmark(benchmark) => {
                    println!("基准测试结果:");
                    println!("  - 吞吐量: {:.2} req/s", benchmark.throughput_per_second);
                    println!(
                        "  - 平均响应时间: {:.2} ms",
                        benchmark.average_response_time
                    );
                    println!("  - 错误率: {:.2}%", benchmark.error_rate);
                }
                OptimizationResult::Memory(memory) => {
                    println!("内存优化结果:");
                    println!("  - 内存节省: {:.2} MB", memory.memory_saved_mb);
                    println!("  - 碎片减少: {:.2}%", memory.fragmentation_reduced_percent);
                }
                OptimizationResult::Concurrency(concurrency) => {
                    println!("并发优化结果:");
                    println!(
                        "  - 吞吐量提升: {:.1}%",
                        concurrency.throughput_improvement_percent
                    );
                    println!(
                        "  - 延迟减少: {:.1}%",
                        concurrency.latency_reduction_percent
                    );
                }
            }
        }

        Ok(())
    }

    /// 演示性能建议
    pub async fn demo_performance_recommendations(&self) -> Result<()> {
        println!("\n💡 演示性能建议:");
        println!("================================");

        let recommendations = self.manager.get_performance_recommendations().await;

        for (i, recommendation) in recommendations.iter().enumerate() {
            println!(
                "{}. {} ({})",
                i + 1,
                recommendation.title,
                recommendation.category
            );
            println!("   描述: {}", recommendation.description);
            println!("   预期改进: {}", recommendation.expected_improvement);
            println!("   实施难度: {}", recommendation.implementation_effort);
            println!("   优先级: {:?}", recommendation.priority);
            println!();
        }

        // 按优先级排序建议
        let mut sorted_recommendations = recommendations.clone();
        sorted_recommendations.sort_by(|a, b| {
            use RecommendationPriority::*;
            match (&a.priority, &b.priority) {
                (Critical, Critical) => std::cmp::Ordering::Equal,
                (Critical, _) => std::cmp::Ordering::Less,
                (_, Critical) => std::cmp::Ordering::Greater,
                (High, High) => std::cmp::Ordering::Equal,
                (High, _) => std::cmp::Ordering::Less,
                (_, High) => std::cmp::Ordering::Greater,
                (Medium, Medium) => std::cmp::Ordering::Equal,
                (Medium, _) => std::cmp::Ordering::Less,
                (_, Medium) => std::cmp::Ordering::Greater,
                (Low, Low) => std::cmp::Ordering::Equal,
            }
        });

        println!("按优先级排序的建议:");
        for (i, recommendation) in sorted_recommendations.iter().enumerate() {
            println!(
                "{}. {} ({:?})",
                i + 1,
                recommendation.title,
                recommendation.priority
            );
        }

        Ok(())
    }

    /// 演示性能监控
    pub async fn demo_performance_monitoring(&self) -> Result<()> {
        println!("\n📊 演示性能监控:");
        println!("================================");

        // 模拟性能指标收集
        let mut metrics = Vec::new();

        for i in 0..10 {
            let metric = PerformanceMetric {
                id: uuid::Uuid::new_v4().to_string(),
                timestamp: chrono::Utc::now(),
                metric_type: PerformanceMetricType::ResponseTime,
                value: 50.0 + (i as f64 * 5.0),
                unit: "ms".to_string(),
                tags: HashMap::from([
                    ("service".to_string(), "demo-service".to_string()),
                    ("endpoint".to_string(), "/api/test".to_string()),
                ]),
                metadata: HashMap::new(),
            };
            metrics.push(metric);
        }

        // 分析性能趋势
        self.analyze_performance_trends(&metrics).await?;

        // 生成性能报告
        self.generate_performance_report(&metrics).await?;

        Ok(())
    }

    /// 分析性能趋势
    async fn analyze_performance_trends(&self, metrics: &[PerformanceMetric]) -> Result<()> {
        println!("性能趋势分析:");

        if metrics.len() < 2 {
            println!("数据点不足，无法分析趋势");
            return Ok(());
        }

        let first_value = metrics[0].value;
        let last_value = metrics[metrics.len() - 1].value;
        let trend = if last_value > first_value {
            "上升"
        } else if last_value < first_value {
            "下降"
        } else {
            "稳定"
        };

        println!("  - 趋势: {}", trend);
        println!("  - 起始值: {:.2} {}", first_value, metrics[0].unit);
        println!("  - 结束值: {:.2} {}", last_value, metrics[0].unit);

        let change_percent = ((last_value - first_value) / first_value) * 100.0;
        println!("  - 变化: {:.1}%", change_percent);

        Ok(())
    }

    /// 生成性能报告
    async fn generate_performance_report(&self, metrics: &[PerformanceMetric]) -> Result<()> {
        println!("\n性能报告:");

        let values: Vec<f64> = metrics.iter().map(|m| m.value).collect();
        let sum: f64 = values.iter().sum();
        let count = values.len() as f64;
        let average = sum / count;

        let min = values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max = values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));

        println!("  - 数据点数: {}", count as usize);
        println!("  - 平均值: {:.2} {}", average, metrics[0].unit);
        println!("  - 最小值: {:.2} {}", min, metrics[0].unit);
        println!("  - 最大值: {:.2} {}", max, metrics[0].unit);

        // 计算标准差
        let variance = values.iter().map(|x| (x - average).powi(2)).sum::<f64>() / count;
        let std_dev = variance.sqrt();
        println!("  - 标准差: {:.2} {}", std_dev, metrics[0].unit);

        Ok(())
    }

    /// 演示性能优化最佳实践
    pub async fn demo_performance_best_practices(&self) -> Result<()> {
        println!("\n📚 演示性能优化最佳实践:");
        println!("================================");

        println!("性能优化最佳实践:");
        println!();

        println!("🚀 基准测试最佳实践:");
        println!("  ✅ 建立性能基线");
        println!("  ✅ 定期运行基准测试");
        println!("  ✅ 监控性能回归");
        println!("  ✅ 设置性能目标");
        println!("  ✅ 分析性能瓶颈");
        println!();

        println!("🧠 内存优化最佳实践:");
        println!("  ✅ 使用对象池减少分配");
        println!("  ✅ 实施内存压缩");
        println!("  ✅ 启用数据去重");
        println!("  ✅ 优化垃圾回收");
        println!("  ✅ 监控内存泄漏");
        println!();

        println!("⚡ 并发优化最佳实践:");
        println!("  ✅ 优化连接池大小");
        println!("  ✅ 调整线程池配置");
        println!("  ✅ 实施批处理");
        println!("  ✅ 使用背压控制");
        println!("  ✅ 实现熔断器");
        println!();

        println!("📊 监控最佳实践:");
        println!("  ✅ 设置关键指标监控");
        println!("  ✅ 实施实时告警");
        println!("  ✅ 定期性能分析");
        println!("  ✅ 建立性能仪表板");
        println!("  ✅ 自动化性能测试");
        println!();

        println!("🔧 工具和框架:");
        println!("  ✅ 使用性能分析工具");
        println!("  ✅ 集成监控系统");
        println!("  ✅ 自动化测试流程");
        println!("  ✅ 持续集成优化");
        println!("  ✅ 性能回归检测");

        Ok(())
    }
}

impl Default for PerformanceOptimizationDemoManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 主函数演示性能优化
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 性能优化演示");
    println!("================================");

    // 创建性能优化演示管理器
    let demo_manager = PerformanceOptimizationDemoManager::new();

    // 演示基准测试
    demo_manager.demo_benchmark_testing().await?;

    // 演示内存优化
    demo_manager.demo_memory_optimization().await?;

    // 演示并发优化
    demo_manager.demo_concurrency_optimization().await?;

    // 演示全面性能优化
    demo_manager.demo_comprehensive_optimization().await?;

    // 演示性能建议
    demo_manager.demo_performance_recommendations().await?;

    // 演示性能监控
    demo_manager.demo_performance_monitoring().await?;

    // 演示性能优化最佳实践
    demo_manager.demo_performance_best_practices().await?;

    println!("\n✅ 性能优化演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 基准测试: 全面的性能基准测试");
    println!("- 内存优化: 对象池、压缩、去重");
    println!("- 并发优化: 连接池、线程池、批处理");
    println!("- 性能监控: 实时指标收集和分析");
    println!("- 优化建议: 智能性能优化建议");
    println!("- 性能分析: 深度性能分析和报告");
    println!();
    println!("📚 性能优化价值:");
    println!("- 提升系统性能");
    println!("- 降低资源消耗");
    println!("- 改善用户体验");
    println!("- 减少运营成本");
    println!("- 提高系统稳定性");
    println!("- 支持业务增长");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_benchmark_demo() {
        let demo_manager = PerformanceOptimizationDemoManager::new();
        let result = demo_manager.demo_benchmark_testing().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_memory_optimization_demo() {
        let demo_manager = PerformanceOptimizationDemoManager::new();
        let result = demo_manager.demo_memory_optimization().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_concurrency_optimization_demo() {
        let demo_manager = PerformanceOptimizationDemoManager::new();
        let result = demo_manager.demo_concurrency_optimization().await;
        assert!(result.is_ok());
    }
}
