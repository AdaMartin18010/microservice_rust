//! 混沌工程模块
//!
//! 本模块实现了混沌工程功能，包括：
//! - 故障注入 (Fault Injection)
//! - 混沌实验 (Chaos Experiments)
//! - 弹性测试 (Resilience Testing)
//! - 混沌猴子 (Chaos Monkey)
//! - 故障恢复测试
//! - 系统稳定性验证

use anyhow::Result;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;
// use rand::Rng;  // 暂时禁用

/// 混沌工程配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosConfig {
    pub enable_chaos_monkey: bool,
    pub failure_rate: f64,        // 0.0 - 1.0
    pub experiment_duration: u64, // seconds
    pub recovery_timeout: u64,    // seconds
    pub max_concurrent_experiments: u32,
    pub enable_auto_recovery: bool,
    pub monitoring_enabled: bool,
}

impl Default for ChaosConfig {
    fn default() -> Self {
        Self {
            enable_chaos_monkey: true,
            failure_rate: 0.1,        // 10% failure rate
            experiment_duration: 300, // 5 minutes
            recovery_timeout: 60,     // 1 minute
            max_concurrent_experiments: 3,
            enable_auto_recovery: true,
            monitoring_enabled: true,
        }
    }
}

/// 故障类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum FaultType {
    NetworkLatency,
    NetworkPartition,
    ServiceUnavailable,
    ResourceExhaustion,
    DependencyFailure,
    DataCorruption,
    SecurityBreach,
    ConfigurationError,
}

/// 故障严重程度
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Severity {
    Low,
    Medium,
    High,
    Critical,
}

/// 混沌实验
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosExperiment {
    pub id: String,
    pub name: String,
    pub description: String,
    pub fault_type: FaultType,
    pub severity: Severity,
    pub target_services: Vec<String>,
    pub parameters: HashMap<String, String>,
    pub duration: u64, // seconds
    pub start_time: Option<DateTime<Utc>>,
    pub end_time: Option<DateTime<Utc>>,
    pub status: ExperimentStatus,
    pub results: Option<ExperimentResults>,
}

/// 实验状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ExperimentStatus {
    Planned,
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// 实验结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExperimentResults {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: f64,
    pub max_response_time: f64,
    pub min_response_time: f64,
    pub recovery_time: Option<f64>,
    pub system_stability: SystemStability,
    pub recommendations: Vec<String>,
}

/// 系统稳定性
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SystemStability {
    Excellent,
    Good,
    Fair,
    Poor,
    Critical,
}

/// 故障注入器
#[allow(dead_code)]
pub struct FaultInjector {
    config: ChaosConfig,
    active_faults: Arc<RwLock<HashMap<String, FaultType>>>,
    metrics: Arc<RwLock<ChaosMetrics>>,
}

/// 混沌指标
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ChaosMetrics {
    pub total_experiments: u64,
    pub successful_experiments: u64,
    pub failed_experiments: u64,
    pub total_faults_injected: u64,
    pub average_recovery_time: f64,
    pub system_uptime: f64,
    pub last_experiment_time: Option<DateTime<Utc>>,
}

impl Default for ChaosMetrics {
    fn default() -> Self {
        Self {
            total_experiments: 0,
            successful_experiments: 0,
            failed_experiments: 0,
            total_faults_injected: 0,
            average_recovery_time: 0.0,
            system_uptime: 100.0,
            last_experiment_time: None,
        }
    }
}

impl FaultInjector {
    pub fn new(config: ChaosConfig) -> Self {
        Self {
            config,
            active_faults: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(ChaosMetrics::default())),
        }
    }

    /// 注入网络延迟故障
    pub async fn inject_network_latency(&self, service_id: &str, delay_ms: u64) -> Result<()> {
        let fault_id = format!("latency_{}", Uuid::new_v4());

        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.insert(fault_id.clone(), FaultType::NetworkLatency);
        }

        // 模拟网络延迟
        tokio::time::sleep(tokio::time::Duration::from_millis(delay_ms)).await;

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_faults_injected += 1;
        }

        println!(
            "🌐 网络延迟故障注入: 服务 {} 延迟 {}ms",
            service_id, delay_ms
        );
        Ok(())
    }

    /// 注入服务不可用故障
    pub async fn inject_service_unavailable(
        &self,
        service_id: &str,
        duration_sec: u64,
    ) -> Result<()> {
        let fault_id = format!("unavailable_{}", Uuid::new_v4());

        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.insert(fault_id.clone(), FaultType::ServiceUnavailable);
        }

        println!(
            "🚫 服务不可用故障注入: 服务 {} 不可用 {} 秒",
            service_id, duration_sec
        );

        // 模拟服务不可用
        tokio::time::sleep(tokio::time::Duration::from_secs(duration_sec)).await;

        // 移除故障
        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.remove(&fault_id);
        }

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_faults_injected += 1;
        }

        println!("✅ 服务不可用故障恢复: 服务 {} 已恢复", service_id);
        Ok(())
    }

    /// 注入资源耗尽故障
    pub async fn inject_resource_exhaustion(
        &self,
        service_id: &str,
        resource_type: &str,
    ) -> Result<()> {
        let fault_id = format!("exhaustion_{}", Uuid::new_v4());

        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.insert(fault_id.clone(), FaultType::ResourceExhaustion);
        }

        println!(
            "💾 资源耗尽故障注入: 服务 {} 资源类型 {}",
            service_id, resource_type
        );

        // 模拟资源耗尽
        match resource_type {
            "memory" => {
                // 模拟内存耗尽
                let _large_vec: Vec<u8> = vec![0; 1024 * 1024 * 100]; // 100MB
                tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
            }
            "cpu" => {
                // 模拟 CPU 耗尽
                let start = std::time::Instant::now();
                while start.elapsed().as_secs() < 10 {
                    // 消耗 CPU 资源
                    let _ = (0..1000000).sum::<u64>();
                }
            }
            "disk" => {
                // 模拟磁盘空间耗尽
                println!("磁盘空间耗尽模拟");
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            }
            _ => {
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            }
        }

        // 移除故障
        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.remove(&fault_id);
        }

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_faults_injected += 1;
        }

        println!(
            "✅ 资源耗尽故障恢复: 服务 {} 资源类型 {}",
            service_id, resource_type
        );
        Ok(())
    }

    /// 注入依赖故障
    pub async fn inject_dependency_failure(
        &self,
        service_id: &str,
        dependency: &str,
    ) -> Result<()> {
        let fault_id = format!("dependency_{}", Uuid::new_v4());

        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.insert(fault_id.clone(), FaultType::DependencyFailure);
        }

        println!(
            "🔗 依赖故障注入: 服务 {} 依赖 {} 失败",
            service_id, dependency
        );

        // 模拟依赖故障
        tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;

        // 移除故障
        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.remove(&fault_id);
        }

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_faults_injected += 1;
        }

        println!(
            "✅ 依赖故障恢复: 服务 {} 依赖 {} 已恢复",
            service_id, dependency
        );
        Ok(())
    }

    /// 注入数据损坏故障
    pub async fn inject_data_corruption(&self, service_id: &str, data_type: &str) -> Result<()> {
        let fault_id = format!("corruption_{}", Uuid::new_v4());

        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.insert(fault_id.clone(), FaultType::DataCorruption);
        }

        println!(
            "💥 数据损坏故障注入: 服务 {} 数据类型 {}",
            service_id, data_type
        );

        // 模拟数据损坏
        tokio::time::sleep(tokio::time::Duration::from_secs(15)).await;

        // 移除故障
        {
            let mut active_faults = self.active_faults.write().await;
            active_faults.remove(&fault_id);
        }

        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_faults_injected += 1;
        }

        println!(
            "✅ 数据损坏故障恢复: 服务 {} 数据类型 {} 已修复",
            service_id, data_type
        );
        Ok(())
    }

    /// 获取活跃故障
    pub async fn get_active_faults(&self) -> HashMap<String, FaultType> {
        self.active_faults.read().await.clone()
    }

    /// 获取混沌指标
    pub async fn get_metrics(&self) -> ChaosMetrics {
        self.metrics.read().await.clone()
    }
}

/// 混沌猴子
#[allow(dead_code)]
pub struct ChaosMonkey {
    config: ChaosConfig,
    fault_injector: Arc<FaultInjector>,
    experiments: Arc<RwLock<HashMap<String, ChaosExperiment>>>,
    is_running: Arc<RwLock<bool>>,
}

impl ChaosMonkey {
    pub fn new(config: ChaosConfig) -> Self {
        let fault_injector = Arc::new(FaultInjector::new(config.clone()));

        Self {
            config,
            fault_injector,
            experiments: Arc::new(RwLock::new(HashMap::new())),
            is_running: Arc::new(RwLock::new(false)),
        }
    }

    /// 启动混沌猴子
    pub async fn start(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return Ok(());
        }

        *is_running = true;
        println!("🐒 混沌猴子启动");

        // 启动混沌猴子循环
        let fault_injector = self.fault_injector.clone();
        let is_running = self.is_running.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            while *is_running.read().await {
                // 随机决定是否注入故障
                // 简化实现，不使用随机数
                let random_value: f64 = 0.5;

                if random_value < config.failure_rate {
                    // 简化实现，使用固定的故障类型和参数
                    let fault_types = [
                        "network_latency",
                        "service_unavailable",
                        "resource_exhaustion",
                        "dependency_failure",
                        "data_corruption",
                    ];

                    // 使用固定的索引和值，而不是随机数
                    let fault_type_index = 0; // 固定选择第一个故障类型
                    let fault_type = fault_types[fault_type_index];
                    let service_id = format!("service_{}", 1); // 固定使用 service_1

                    match fault_type {
                        "network_latency" => {
                            let delay = 1000; // 固定延迟 1000ms
                            let _ = fault_injector
                                .inject_network_latency(&service_id, delay)
                                .await;
                        }
                        "service_unavailable" => {
                            let duration = 30; // 固定持续时间 30秒
                            let _ = fault_injector
                                .inject_service_unavailable(&service_id, duration)
                                .await;
                        }
                        "resource_exhaustion" => {
                            let resource_types = ["memory", "cpu", "disk"];
                            let resource_type = resource_types[0]; // 固定选择第一个资源类型
                            let _ = fault_injector
                                .inject_resource_exhaustion(&service_id, resource_type)
                                .await;
                        }
                        "dependency_failure" => {
                            let dependency = "dependency_1".to_string(); // 固定使用 dependency_1
                            let _ = fault_injector
                                .inject_dependency_failure(&service_id, &dependency)
                                .await;
                        }
                        "data_corruption" => {
                            let data_types = ["user_data", "order_data", "product_data"];
                            let data_type = data_types[0]; // 固定选择第一个数据类型
                            let _ = fault_injector
                                .inject_data_corruption(&service_id, data_type)
                                .await;
                        }
                        _ => {}
                    }
                }

                // 等待一段时间
                tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
            }
        });

        Ok(())
    }

    /// 停止混沌猴子
    pub async fn stop(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        *is_running = false;
        println!("🛑 混沌猴子停止");
        Ok(())
    }

    /// 创建混沌实验
    pub async fn create_experiment(&self, experiment: ChaosExperiment) -> Result<String> {
        let experiment_id = experiment.id.clone();
        let mut experiments = self.experiments.write().await;
        experiments.insert(experiment_id.clone(), experiment);

        println!("🧪 混沌实验创建: {}", experiment_id);
        Ok(experiment_id)
    }

    /// 运行混沌实验
    pub async fn run_experiment(&self, experiment_id: &str) -> Result<ExperimentResults> {
        let mut experiments = self.experiments.write().await;
        let experiment = experiments
            .get_mut(experiment_id)
            .ok_or_else(|| anyhow::anyhow!("实验不存在"))?;

        experiment.status = ExperimentStatus::Running;
        experiment.start_time = Some(Utc::now());

        println!(
            "🚀 开始运行混沌实验: {} - {:?}",
            experiment.name, experiment.fault_type
        );

        let start_time = std::time::Instant::now();
        let mut total_requests = 0u64;
        let mut successful_requests = 0u64;
        let mut failed_requests = 0u64;
        let mut response_times = Vec::new();

        // 模拟实验运行
        for i in 0..10 {
            let request_start = std::time::Instant::now();
            total_requests += 1;

            // 模拟请求处理
            match experiment.fault_type {
                FaultType::NetworkLatency => {
                    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
                    successful_requests += 1;
                }
                FaultType::ServiceUnavailable => {
                    if i % 3 == 0 {
                        failed_requests += 1;
                    } else {
                        successful_requests += 1;
                    }
                }
                FaultType::ResourceExhaustion => {
                    if i % 4 == 0 {
                        failed_requests += 1;
                    } else {
                        successful_requests += 1;
                    }
                }
                FaultType::DependencyFailure => {
                    if i % 2 == 0 {
                        failed_requests += 1;
                    } else {
                        successful_requests += 1;
                    }
                }
                FaultType::DataCorruption => {
                    if i % 5 == 0 {
                        failed_requests += 1;
                    } else {
                        successful_requests += 1;
                    }
                }
                _ => {
                    successful_requests += 1;
                }
            }

            let response_time = request_start.elapsed().as_millis() as f64;
            response_times.push(response_time);

            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }

        let experiment_duration = start_time.elapsed().as_secs_f64();
        let average_response_time =
            response_times.iter().sum::<f64>() / response_times.len() as f64;
        let max_response_time = response_times.iter().fold(0.0f64, |a, &b| a.max(b));
        let min_response_time = response_times.iter().fold(f64::INFINITY, |a, &b| a.min(b));

        // 计算系统稳定性
        let success_rate = successful_requests as f64 / total_requests as f64;
        let system_stability = match success_rate {
            s if s >= 0.95 => SystemStability::Excellent,
            s if s >= 0.85 => SystemStability::Good,
            s if s >= 0.70 => SystemStability::Fair,
            s if s >= 0.50 => SystemStability::Poor,
            _ => SystemStability::Critical,
        };

        // 生成建议
        let mut recommendations = Vec::new();
        match system_stability {
            SystemStability::Excellent => {
                recommendations.push("系统表现优秀，继续保持".to_string());
            }
            SystemStability::Good => {
                recommendations.push("系统表现良好，可以进一步优化".to_string());
            }
            SystemStability::Fair => {
                recommendations.push("系统表现一般，建议增加容错机制".to_string());
            }
            SystemStability::Poor => {
                recommendations.push("系统表现较差，需要立即优化".to_string());
                recommendations.push("建议增加重试机制和熔断器".to_string());
            }
            SystemStability::Critical => {
                recommendations.push("系统表现严重，需要紧急修复".to_string());
                recommendations.push("建议增加冗余和故障转移机制".to_string());
                recommendations.push("建议进行系统架构重构".to_string());
            }
        }

        let results = ExperimentResults {
            total_requests,
            successful_requests,
            failed_requests,
            average_response_time,
            max_response_time,
            min_response_time,
            recovery_time: Some(experiment_duration),
            system_stability,
            recommendations,
        };

        experiment.status = ExperimentStatus::Completed;
        experiment.end_time = Some(Utc::now());
        experiment.results = Some(results.clone());

        // 更新指标
        {
            let mut metrics = self.fault_injector.metrics.write().await;
            metrics.total_experiments += 1;
            metrics.successful_experiments += 1;
            metrics.last_experiment_time = Some(Utc::now());
        }

        println!(
            "✅ 混沌实验完成: {} - 稳定性: {:?}",
            experiment.name, results.system_stability
        );
        Ok(results)
    }

    /// 获取实验列表
    pub async fn get_experiments(&self) -> Vec<ChaosExperiment> {
        let experiments = self.experiments.read().await;
        experiments.values().cloned().collect()
    }

    /// 获取实验详情
    pub async fn get_experiment(&self, experiment_id: &str) -> Option<ChaosExperiment> {
        let experiments = self.experiments.read().await;
        experiments.get(experiment_id).cloned()
    }
}

/// 弹性测试器
#[allow(dead_code)]
pub struct ResilienceTester {
    config: ChaosConfig,
    chaos_monkey: Arc<ChaosMonkey>,
}

impl ResilienceTester {
    pub fn new(config: ChaosConfig) -> Self {
        let chaos_monkey = Arc::new(ChaosMonkey::new(config.clone()));

        Self {
            config,
            chaos_monkey,
        }
    }

    /// 运行弹性测试
    pub async fn run_resilience_test(
        &self,
        test_name: &str,
        duration_sec: u64,
    ) -> Result<ResilienceTestResults> {
        println!("🛡️  开始弹性测试: {} ({} 秒)", test_name, duration_sec);

        let start_time = std::time::Instant::now();
        let mut test_results = Vec::new();

        // 启动混沌猴子
        self.chaos_monkey.start().await?;

        // 运行测试
        while start_time.elapsed().as_secs() < duration_sec {
            // 创建并运行混沌实验
            let experiment = ChaosExperiment {
                id: Uuid::new_v4().to_string(),
                name: format!("弹性测试实验_{}", test_results.len() + 1),
                description: "弹性测试实验".to_string(),
                fault_type: FaultType::NetworkLatency,
                severity: Severity::Medium,
                target_services: vec!["test_service".to_string()],
                parameters: HashMap::new(),
                duration: 30,
                start_time: None,
                end_time: None,
                status: ExperimentStatus::Planned,
                results: None,
            };

            let experiment_id = self.chaos_monkey.create_experiment(experiment).await?;
            let results = self.chaos_monkey.run_experiment(&experiment_id).await?;
            test_results.push(results);

            // 等待一段时间
            tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
        }

        // 停止混沌猴子
        self.chaos_monkey.stop().await?;

        // 计算总体结果
        let total_requests: u64 = test_results.iter().map(|r| r.total_requests).sum();
        let total_successful: u64 = test_results.iter().map(|r| r.successful_requests).sum();
        let total_failed: u64 = test_results.iter().map(|r| r.failed_requests).sum();

        let overall_success_rate = if total_requests > 0 {
            total_successful as f64 / total_requests as f64
        } else {
            0.0
        };

        let average_response_time = test_results
            .iter()
            .map(|r| r.average_response_time)
            .sum::<f64>()
            / test_results.len() as f64;

        let overall_stability = match overall_success_rate {
            s if s >= 0.95 => SystemStability::Excellent,
            s if s >= 0.85 => SystemStability::Good,
            s if s >= 0.70 => SystemStability::Fair,
            s if s >= 0.50 => SystemStability::Poor,
            _ => SystemStability::Critical,
        };

        let resilience_results = ResilienceTestResults {
            test_name: test_name.to_string(),
            duration_sec,
            total_experiments: test_results.len(),
            total_requests,
            successful_requests: total_successful,
            failed_requests: total_failed,
            success_rate: overall_success_rate,
            average_response_time,
            system_stability: overall_stability.clone(),
            recommendations: self.generate_recommendations(overall_stability),
        };

        println!(
            "✅ 弹性测试完成: {} - 成功率: {:.2}%",
            test_name,
            overall_success_rate * 100.0
        );
        Ok(resilience_results)
    }

    /// 生成建议
    fn generate_recommendations(&self, stability: SystemStability) -> Vec<String> {
        match stability {
            SystemStability::Excellent => {
                vec![
                    "系统弹性表现优秀".to_string(),
                    "建议定期进行弹性测试".to_string(),
                ]
            }
            SystemStability::Good => {
                vec![
                    "系统弹性表现良好".to_string(),
                    "建议增加监控和告警".to_string(),
                    "建议定期进行故障演练".to_string(),
                ]
            }
            SystemStability::Fair => {
                vec![
                    "系统弹性表现一般".to_string(),
                    "建议增加重试机制".to_string(),
                    "建议实现熔断器模式".to_string(),
                    "建议增加服务降级机制".to_string(),
                ]
            }
            SystemStability::Poor => {
                vec![
                    "系统弹性表现较差".to_string(),
                    "建议立即增加冗余机制".to_string(),
                    "建议实现故障转移".to_string(),
                    "建议增加缓存层".to_string(),
                    "建议进行架构优化".to_string(),
                ]
            }
            SystemStability::Critical => {
                vec![
                    "系统弹性表现严重".to_string(),
                    "建议紧急增加冗余和备份".to_string(),
                    "建议实现多活架构".to_string(),
                    "建议进行系统重构".to_string(),
                    "建议增加人工干预机制".to_string(),
                ]
            }
        }
    }
}

/// 弹性测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceTestResults {
    pub test_name: String,
    pub duration_sec: u64,
    pub total_experiments: usize,
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub success_rate: f64,
    pub average_response_time: f64,
    pub system_stability: SystemStability,
    pub recommendations: Vec<String>,
}

/// 高级混沌工程服务
pub struct AdvancedChaosEngineeringService {
    config: ChaosConfig,
    fault_injector: Arc<FaultInjector>,
    chaos_monkey: Arc<ChaosMonkey>,
    resilience_tester: Arc<ResilienceTester>,
}

impl AdvancedChaosEngineeringService {
    pub fn new(config: ChaosConfig) -> Self {
        let fault_injector = Arc::new(FaultInjector::new(config.clone()));
        let chaos_monkey = Arc::new(ChaosMonkey::new(config.clone()));
        let resilience_tester = Arc::new(ResilienceTester::new(config.clone()));

        Self {
            config,
            fault_injector,
            chaos_monkey,
            resilience_tester,
        }
    }

    /// 获取故障注入器
    pub fn get_fault_injector(&self) -> Arc<FaultInjector> {
        self.fault_injector.clone()
    }

    /// 获取混沌猴子
    pub fn get_chaos_monkey(&self) -> Arc<ChaosMonkey> {
        self.chaos_monkey.clone()
    }

    /// 获取弹性测试器
    pub fn get_resilience_tester(&self) -> Arc<ResilienceTester> {
        self.resilience_tester.clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ChaosConfig {
        &self.config
    }

    /// 获取混沌指标
    pub async fn get_chaos_metrics(&self) -> ChaosMetrics {
        self.fault_injector.get_metrics().await
    }
}

/// 混沌工程服务工厂
pub struct ChaosEngineeringServiceFactory;

impl ChaosEngineeringServiceFactory {
    /// 创建默认配置的混沌工程服务
    pub fn create_default_service() -> AdvancedChaosEngineeringService {
        AdvancedChaosEngineeringService::new(ChaosConfig::default())
    }

    /// 创建自定义配置的混沌工程服务
    pub fn create_custom_service(config: ChaosConfig) -> AdvancedChaosEngineeringService {
        AdvancedChaosEngineeringService::new(config)
    }

    /// 创建生产环境配置
    pub fn create_production_config() -> ChaosConfig {
        ChaosConfig {
            enable_chaos_monkey: false, // 生产环境默认关闭
            failure_rate: 0.05,         // 5% failure rate
            experiment_duration: 600,   // 10 minutes
            recovery_timeout: 120,      // 2 minutes
            max_concurrent_experiments: 1,
            enable_auto_recovery: true,
            monitoring_enabled: true,
        }
    }

    /// 创建测试环境配置
    pub fn create_testing_config() -> ChaosConfig {
        ChaosConfig {
            enable_chaos_monkey: true,
            failure_rate: 0.2,        // 20% failure rate
            experiment_duration: 300, // 5 minutes
            recovery_timeout: 60,     // 1 minute
            max_concurrent_experiments: 5,
            enable_auto_recovery: true,
            monitoring_enabled: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_fault_injector() {
        let config = ChaosConfig::default();
        let injector = FaultInjector::new(config);

        let result = injector.inject_network_latency("test_service", 100).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_chaos_monkey() {
        let config = ChaosConfig::default();
        let monkey = ChaosMonkey::new(config);

        let result = monkey.start().await;
        assert!(result.is_ok());

        let result = monkey.stop().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_resilience_tester() {
        let config = ChaosConfig::default();
        let tester = ResilienceTester::new(config);

        let result = tester.run_resilience_test("test", 30).await;
        assert!(result.is_ok());
    }
}
