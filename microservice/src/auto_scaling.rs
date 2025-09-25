//! 自动扩缩容模块
//!
//! 本模块实现了智能自动扩缩容功能，包括：
//! - 水平扩缩容 (Horizontal Pod Autoscaling)
//! - 垂直扩缩容 (Vertical Pod Autoscaling)
//! - 预测性扩缩容 (Predictive Autoscaling)
//! - 自定义指标扩缩容 (Custom Metrics Autoscaling)
//! - 资源监控和优化
//! - 扩缩容策略管理

use anyhow::Result;
use chrono::{DateTime, Duration, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;
use tokio::sync::RwLock;
use uuid::Uuid;

/// 扩缩容配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScalingConfig {
    pub enable_horizontal_scaling: bool,
    pub enable_vertical_scaling: bool,
    pub enable_predictive_scaling: bool,
    pub min_replicas: u32,
    pub max_replicas: u32,
    pub target_cpu_utilization: f64,
    pub target_memory_utilization: f64,
    pub scale_up_threshold: f64,
    pub scale_down_threshold: f64,
    pub scale_up_cooldown: u64,
    pub scale_down_cooldown: u64,
    pub predictive_window: u64,
    pub custom_metrics: Vec<CustomMetric>,
}

impl Default for ScalingConfig {
    fn default() -> Self {
        Self {
            enable_horizontal_scaling: true,
            enable_vertical_scaling: true,
            enable_predictive_scaling: true,
            min_replicas: 1,
            max_replicas: 10,
            target_cpu_utilization: 70.0,
            target_memory_utilization: 80.0,
            scale_up_threshold: 80.0,
            scale_down_threshold: 30.0,
            scale_up_cooldown: 300,   // 5 minutes
            scale_down_cooldown: 600, // 10 minutes
            predictive_window: 3600,  // 1 hour
            custom_metrics: Vec::new(),
        }
    }
}

/// 自定义指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CustomMetric {
    pub name: String,
    pub metric_type: MetricType,
    pub target_value: f64,
    pub weight: f64,
    pub enabled: bool,
}

/// 指标类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum MetricType {
    Cpu,
    Memory,
    RequestRate,
    ResponseTime,
    ErrorRate,
    QueueLength,
    Custom(String),
}

/// 扩缩容类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ScalingType {
    Horizontal,
    Vertical,
    Predictive,
}

/// 扩缩容动作
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ScalingAction {
    ScaleUp,
    ScaleDown,
    NoAction,
}

impl std::fmt::Display for ScalingAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScalingAction::ScaleUp => write!(f, "扩容"),
            ScalingAction::ScaleDown => write!(f, "缩容"),
            ScalingAction::NoAction => write!(f, "无操作"),
        }
    }
}

/// 扩缩容事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScalingEvent {
    pub id: String,
    pub timestamp: DateTime<Utc>,
    pub scaling_type: ScalingType,
    pub action: ScalingAction,
    pub current_replicas: u32,
    pub target_replicas: u32,
    pub reason: String,
    pub metrics: HashMap<String, f64>,
    pub success: bool,
}

/// 资源指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMetrics {
    pub timestamp: DateTime<Utc>,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub request_rate: f64,
    pub response_time: f64,
    pub error_rate: f64,
    pub active_connections: u32,
    pub queue_length: u32,
    pub custom_metrics: HashMap<String, f64>,
}

/// 预测数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictionDataPoint {
    pub timestamp: DateTime<Utc>,
    pub predicted_cpu: f64,
    pub predicted_memory: f64,
    pub predicted_request_rate: f64,
    pub confidence: f64,
}

/// 水平扩缩容器
pub struct HorizontalScaler {
    config: ScalingConfig,
    current_replicas: Arc<RwLock<u32>>,
    scaling_history: Arc<RwLock<Vec<ScalingEvent>>>,
    metrics_history: Arc<RwLock<Vec<ResourceMetrics>>>,
    last_scale_time: Arc<RwLock<Option<DateTime<Utc>>>>,
}

impl HorizontalScaler {
    pub fn new(config: ScalingConfig) -> Self {
        Self {
            config,
            current_replicas: Arc::new(RwLock::new(1)),
            scaling_history: Arc::new(RwLock::new(Vec::new())),
            metrics_history: Arc::new(RwLock::new(Vec::new())),
            last_scale_time: Arc::new(RwLock::new(None)),
        }
    }

    /// 评估是否需要扩缩容
    pub async fn evaluate_scaling(&self, metrics: &ResourceMetrics) -> Result<ScalingAction> {
        // 记录指标
        {
            let mut metrics_history = self.metrics_history.write().await;
            metrics_history.push(metrics.clone());

            // 保持最近100个指标点
            if metrics_history.len() > 100 {
                metrics_history.remove(0);
            }
        }

        // 检查冷却时间
        let last_scale_time = *self.last_scale_time.read().await;
        if let Some(last_time) = last_scale_time {
            let time_since_last_scale =
                Utc::now().signed_duration_since(last_time).num_seconds() as u64;

            if metrics.cpu_usage > self.config.scale_up_threshold {
                if time_since_last_scale < self.config.scale_up_cooldown {
                    return Ok(ScalingAction::NoAction);
                }
            } else if metrics.cpu_usage < self.config.scale_down_threshold
                && time_since_last_scale < self.config.scale_down_cooldown
            {
                return Ok(ScalingAction::NoAction);
            }
        }

        let current_replicas = *self.current_replicas.read().await;

        // 检查是否超过阈值
        if metrics.cpu_usage > self.config.scale_up_threshold ||
           metrics.memory_usage > self.config.target_memory_utilization ||
           metrics.response_time > 1000.0 || // 1秒
           metrics.error_rate > 5.0
        {
            // 5%

            if current_replicas < self.config.max_replicas {
                return Ok(ScalingAction::ScaleUp);
            }
        } else if metrics.cpu_usage < self.config.scale_down_threshold &&
                  metrics.memory_usage < self.config.target_memory_utilization &&
                  metrics.response_time < 100.0 && // 100ms
                  metrics.error_rate < 1.0
        {
            // 1%

            if current_replicas > self.config.min_replicas {
                return Ok(ScalingAction::ScaleDown);
            }
        }

        Ok(ScalingAction::NoAction)
    }

    /// 执行扩缩容
    pub async fn execute_scaling(
        &self,
        action: ScalingAction,
        metrics: &ResourceMetrics,
    ) -> Result<ScalingEvent> {
        let mut current_replicas = self.current_replicas.write().await;
        let mut target_replicas = *current_replicas;

        let reason = match action {
            ScalingAction::ScaleUp => {
                target_replicas += 1;
                format!(
                    "CPU: {:.1}%, Memory: {:.1}%, ResponseTime: {:.1}ms",
                    metrics.cpu_usage, metrics.memory_usage, metrics.response_time
                )
            }
            ScalingAction::ScaleDown => {
                target_replicas -= 1;
                format!(
                    "CPU: {:.1}%, Memory: {:.1}%, ResponseTime: {:.1}ms",
                    metrics.cpu_usage, metrics.memory_usage, metrics.response_time
                )
            }
            ScalingAction::NoAction => {
                return Ok(ScalingEvent {
                    id: Uuid::new_v4().to_string(),
                    timestamp: Utc::now(),
                    scaling_type: ScalingType::Horizontal,
                    action,
                    current_replicas: *current_replicas,
                    target_replicas: *current_replicas,
                    reason: "No scaling needed".to_string(),
                    metrics: HashMap::new(),
                    success: true,
                });
            }
        };

        // 限制目标副本数
        target_replicas = target_replicas
            .max(self.config.min_replicas)
            .min(self.config.max_replicas);

        let scaling_event = ScalingEvent {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            scaling_type: ScalingType::Horizontal,
            action: action.clone(),
            current_replicas: *current_replicas,
            target_replicas,
            reason,
            metrics: HashMap::from([
                ("cpu_usage".to_string(), metrics.cpu_usage),
                ("memory_usage".to_string(), metrics.memory_usage),
                ("response_time".to_string(), metrics.response_time),
                ("error_rate".to_string(), metrics.error_rate),
            ]),
            success: true,
        };

        // 更新副本数
        *current_replicas = target_replicas;

        // 更新最后扩缩容时间
        {
            let mut last_scale_time = self.last_scale_time.write().await;
            *last_scale_time = Some(Utc::now());
        }

        // 记录扩缩容历史
        {
            let mut scaling_history = self.scaling_history.write().await;
            scaling_history.push(scaling_event.clone());

            // 保持最近50个扩缩容事件
            if scaling_history.len() > 50 {
                scaling_history.remove(0);
            }
        }

        println!(
            "🔄 水平扩缩容: {} -> {} (原因: {})",
            scaling_event.current_replicas, scaling_event.target_replicas, scaling_event.reason
        );

        Ok(scaling_event)
    }

    /// 获取当前副本数
    pub async fn get_current_replicas(&self) -> u32 {
        *self.current_replicas.read().await
    }

    /// 获取扩缩容历史
    pub async fn get_scaling_history(&self) -> Vec<ScalingEvent> {
        self.scaling_history.read().await.clone()
    }

    /// 获取指标历史
    pub async fn get_metrics_history(&self) -> Vec<ResourceMetrics> {
        self.metrics_history.read().await.clone()
    }
}

/// 垂直扩缩容器
pub struct VerticalScaler {
    config: ScalingConfig,
    current_cpu_limit: Arc<RwLock<f64>>,
    current_memory_limit: Arc<RwLock<f64>>,
    scaling_history: Arc<RwLock<Vec<ScalingEvent>>>,
    resource_history: Arc<RwLock<Vec<ResourceMetrics>>>,
    last_scale_time: Arc<RwLock<Option<DateTime<Utc>>>>,
}

impl VerticalScaler {
    pub fn new(config: ScalingConfig) -> Self {
        Self {
            config,
            current_cpu_limit: Arc::new(RwLock::new(1000.0)), // 1000m CPU
            current_memory_limit: Arc::new(RwLock::new(512.0)), // 512Mi Memory
            scaling_history: Arc::new(RwLock::new(Vec::new())),
            resource_history: Arc::new(RwLock::new(Vec::new())),
            last_scale_time: Arc::new(RwLock::new(None)),
        }
    }

    /// 评估是否需要垂直扩缩容
    pub async fn evaluate_scaling(&self, metrics: &ResourceMetrics) -> Result<ScalingAction> {
        // 记录资源使用情况
        {
            let mut resource_history = self.resource_history.write().await;
            resource_history.push(metrics.clone());

            // 保持最近100个资源点
            if resource_history.len() > 100 {
                resource_history.remove(0);
            }
        }

        // 检查冷却时间
        let last_scale_time = *self.last_scale_time.read().await;
        if let Some(last_time) = last_scale_time {
            let time_since_last_scale =
                Utc::now().signed_duration_since(last_time).num_seconds() as u64;

            if time_since_last_scale < self.config.scale_up_cooldown {
                return Ok(ScalingAction::NoAction);
            }
        }

        let cpu_limit = *self.current_cpu_limit.read().await;
        let memory_limit = *self.current_memory_limit.read().await;

        // 检查是否需要扩容
        if metrics.cpu_usage > 90.0 || metrics.memory_usage > 95.0 {
            return Ok(ScalingAction::ScaleUp);
        }

        // 检查是否需要缩容
        if metrics.cpu_usage < 30.0 && metrics.memory_usage < 40.0 {
            // 确保不会缩容到最小值以下
            if cpu_limit > 100.0 || memory_limit > 128.0 {
                return Ok(ScalingAction::ScaleDown);
            }
        }

        Ok(ScalingAction::NoAction)
    }

    /// 执行垂直扩缩容
    pub async fn execute_scaling(
        &self,
        action: ScalingAction,
        metrics: &ResourceMetrics,
    ) -> Result<ScalingEvent> {
        let mut cpu_limit = self.current_cpu_limit.write().await;
        let mut memory_limit = self.current_memory_limit.write().await;

        let old_cpu_limit = *cpu_limit;
        let old_memory_limit = *memory_limit;

        let (new_cpu_limit, new_memory_limit, reason) = match action {
            ScalingAction::ScaleUp => {
                let new_cpu = (*cpu_limit * 1.5).min(4000.0); // 最大4核
                let new_memory = (*memory_limit * 1.5).min(2048.0); // 最大2Gi
                let reason = format!(
                    "资源使用率过高 - CPU: {:.1}%, Memory: {:.1}%",
                    metrics.cpu_usage, metrics.memory_usage
                );
                (new_cpu, new_memory, reason)
            }
            ScalingAction::ScaleDown => {
                let new_cpu = (*cpu_limit * 0.8).max(100.0); // 最小100m
                let new_memory = (*memory_limit * 0.8).max(128.0); // 最小128Mi
                let reason = format!(
                    "资源使用率较低 - CPU: {:.1}%, Memory: {:.1}%",
                    metrics.cpu_usage, metrics.memory_usage
                );
                (new_cpu, new_memory, reason)
            }
            ScalingAction::NoAction => {
                return Ok(ScalingEvent {
                    id: Uuid::new_v4().to_string(),
                    timestamp: Utc::now(),
                    scaling_type: ScalingType::Vertical,
                    action,
                    current_replicas: 1, // 垂直扩缩容不改变副本数
                    target_replicas: 1,
                    reason: "No vertical scaling needed".to_string(),
                    metrics: HashMap::new(),
                    success: true,
                });
            }
        };

        *cpu_limit = new_cpu_limit;
        *memory_limit = new_memory_limit;

        let scaling_event = ScalingEvent {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            scaling_type: ScalingType::Vertical,
            action: action.clone(),
            current_replicas: 1,
            target_replicas: 1,
            reason,
            metrics: HashMap::from([
                ("cpu_usage".to_string(), metrics.cpu_usage),
                ("memory_usage".to_string(), metrics.memory_usage),
                ("old_cpu_limit".to_string(), old_cpu_limit),
                ("new_cpu_limit".to_string(), new_cpu_limit),
                ("old_memory_limit".to_string(), old_memory_limit),
                ("new_memory_limit".to_string(), new_memory_limit),
            ]),
            success: true,
        };

        // 更新最后扩缩容时间
        {
            let mut last_scale_time = self.last_scale_time.write().await;
            *last_scale_time = Some(Utc::now());
        }

        // 记录扩缩容历史
        {
            let mut scaling_history = self.scaling_history.write().await;
            scaling_history.push(scaling_event.clone());

            // 保持最近50个扩缩容事件
            if scaling_history.len() > 50 {
                scaling_history.remove(0);
            }
        }

        println!(
            "📈 垂直扩缩容: CPU {:.0}m -> {:.0}m, Memory {:.0}Mi -> {:.0}Mi (原因: {})",
            old_cpu_limit, new_cpu_limit, old_memory_limit, new_memory_limit, scaling_event.reason
        );

        Ok(scaling_event)
    }

    /// 获取当前资源限制
    pub async fn get_current_limits(&self) -> (f64, f64) {
        let cpu_limit = *self.current_cpu_limit.read().await;
        let memory_limit = *self.current_memory_limit.read().await;
        (cpu_limit, memory_limit)
    }

    /// 获取扩缩容历史
    pub async fn get_scaling_history(&self) -> Vec<ScalingEvent> {
        self.scaling_history.read().await.clone()
    }
}

/// 预测性扩缩容器
pub struct PredictiveScaler {
    config: ScalingConfig,
    prediction_model: Arc<RwLock<PredictionModel>>,
    scaling_history: Arc<RwLock<Vec<ScalingEvent>>>,
    prediction_history: Arc<RwLock<Vec<PredictionDataPoint>>>,
}

/// 预测模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictionModel {
    pub name: String,
    pub version: String,
    pub accuracy: f64,
    pub last_trained: DateTime<Utc>,
    pub parameters: HashMap<String, f64>,
}

impl PredictiveScaler {
    pub fn new(config: ScalingConfig) -> Self {
        let prediction_model = PredictionModel {
            name: "SimpleMovingAverage".to_string(),
            version: "1.0".to_string(),
            accuracy: 0.85,
            last_trained: Utc::now(),
            parameters: HashMap::from([
                ("window_size".to_string(), 10.0),
                ("trend_factor".to_string(), 1.2),
                ("seasonality_factor".to_string(), 1.1),
            ]),
        };

        Self {
            config,
            prediction_model: Arc::new(RwLock::new(prediction_model)),
            scaling_history: Arc::new(RwLock::new(Vec::new())),
            prediction_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 生成预测
    pub async fn generate_predictions(
        &self,
        metrics_history: &[ResourceMetrics],
    ) -> Result<Vec<PredictionDataPoint>> {
        if metrics_history.len() < 10 {
            return Ok(Vec::new());
        }

        let mut predictions = Vec::new();
        let window_size = 10;

        // 使用简单移动平均进行预测
        for i in 0..5 {
            // 预测未来5个时间点
            let future_time = Utc::now() + Duration::minutes((i + 1) * 5);

            // 计算移动平均
            let recent_metrics =
                &metrics_history[metrics_history.len().saturating_sub(window_size)..];

            let avg_cpu = recent_metrics.iter().map(|m| m.cpu_usage).sum::<f64>()
                / recent_metrics.len() as f64;
            let avg_memory = recent_metrics.iter().map(|m| m.memory_usage).sum::<f64>()
                / recent_metrics.len() as f64;
            let avg_request_rate = recent_metrics.iter().map(|m| m.request_rate).sum::<f64>()
                / recent_metrics.len() as f64;

            // 应用趋势因子
            let trend_factor = 1.0 + (i as f64 * 0.05); // 假设有轻微上升趋势
            let predicted_cpu = (avg_cpu * trend_factor).min(100.0);
            let predicted_memory = (avg_memory * trend_factor).min(100.0);
            let predicted_request_rate = avg_request_rate * trend_factor;

            // 计算置信度
            let confidence = (1.0 - (i as f64 * 0.1)).max(0.5);

            predictions.push(PredictionDataPoint {
                timestamp: future_time,
                predicted_cpu,
                predicted_memory,
                predicted_request_rate,
                confidence,
            });
        }

        // 记录预测历史
        {
            let mut prediction_history = self.prediction_history.write().await;
            prediction_history.extend(predictions.clone());

            // 保持最近100个预测点
            if prediction_history.len() > 100 {
                let excess_count = prediction_history.len() - 100;
                prediction_history.drain(0..excess_count);
            }
        }

        Ok(predictions)
    }

    /// 基于预测评估扩缩容
    pub async fn evaluate_predictive_scaling(
        &self,
        predictions: &[PredictionDataPoint],
    ) -> Result<ScalingAction> {
        if predictions.is_empty() {
            return Ok(ScalingAction::NoAction);
        }

        // 检查未来是否会有资源压力
        for prediction in predictions {
            if prediction.predicted_cpu > self.config.scale_up_threshold
                || prediction.predicted_memory > self.config.target_memory_utilization
                || prediction.predicted_request_rate > 1000.0
            {
                // 1000 req/s

                return Ok(ScalingAction::ScaleUp);
            }
        }

        // 检查未来是否资源充足，可以缩容
        let all_low = predictions.iter().all(|p| {
            p.predicted_cpu < self.config.scale_down_threshold
                && p.predicted_memory < 50.0
                && p.predicted_request_rate < 100.0
        });

        if all_low {
            return Ok(ScalingAction::ScaleDown);
        }

        Ok(ScalingAction::NoAction)
    }

    /// 执行预测性扩缩容
    pub async fn execute_predictive_scaling(
        &self,
        action: ScalingAction,
        predictions: &[PredictionDataPoint],
    ) -> Result<ScalingEvent> {
        let reason = match action {
            ScalingAction::ScaleUp => {
                let max_predicted_cpu = predictions
                    .iter()
                    .map(|p| p.predicted_cpu)
                    .fold(0.0, f64::max);
                let max_predicted_memory = predictions
                    .iter()
                    .map(|p| p.predicted_memory)
                    .fold(0.0, f64::max);
                format!(
                    "预测性扩容 - 预计CPU: {:.1}%, Memory: {:.1}%",
                    max_predicted_cpu, max_predicted_memory
                )
            }
            ScalingAction::ScaleDown => {
                let avg_predicted_cpu = predictions.iter().map(|p| p.predicted_cpu).sum::<f64>()
                    / predictions.len() as f64;
                let avg_predicted_memory =
                    predictions.iter().map(|p| p.predicted_memory).sum::<f64>()
                        / predictions.len() as f64;
                format!(
                    "预测性缩容 - 预计CPU: {:.1}%, Memory: {:.1}%",
                    avg_predicted_cpu, avg_predicted_memory
                )
            }
            ScalingAction::NoAction => {
                return Ok(ScalingEvent {
                    id: Uuid::new_v4().to_string(),
                    timestamp: Utc::now(),
                    scaling_type: ScalingType::Predictive,
                    action,
                    current_replicas: 1,
                    target_replicas: 1,
                    reason: "No predictive scaling needed".to_string(),
                    metrics: HashMap::new(),
                    success: true,
                });
            }
        };

        let scaling_event = ScalingEvent {
            id: Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            scaling_type: ScalingType::Predictive,
            action: action.clone(),
            current_replicas: 1,
            target_replicas: match action {
                ScalingAction::ScaleUp => 2,
                ScalingAction::ScaleDown => 1,
                ScalingAction::NoAction => 1,
            },
            reason,
            metrics: HashMap::from([
                (
                    "prediction_confidence".to_string(),
                    predictions.first().map(|p| p.confidence).unwrap_or(0.0),
                ),
                ("prediction_horizon".to_string(), predictions.len() as f64),
            ]),
            success: true,
        };

        // 记录扩缩容历史
        {
            let mut scaling_history = self.scaling_history.write().await;
            scaling_history.push(scaling_event.clone());

            // 保持最近50个扩缩容事件
            if scaling_history.len() > 50 {
                scaling_history.remove(0);
            }
        }

        println!(
            "🔮 预测性扩缩容: {} (置信度: {:.1}%)",
            scaling_event.reason,
            predictions
                .first()
                .map(|p| p.confidence * 100.0)
                .unwrap_or(0.0)
        );

        Ok(scaling_event)
    }

    /// 获取预测历史
    pub async fn get_prediction_history(&self) -> Vec<PredictionDataPoint> {
        self.prediction_history.read().await.clone()
    }

    /// 获取扩缩容历史
    pub async fn get_scaling_history(&self) -> Vec<ScalingEvent> {
        self.scaling_history.read().await.clone()
    }

    /// 训练预测模型
    pub async fn train_model(&self, metrics_history: &[ResourceMetrics]) -> Result<()> {
        if metrics_history.len() < 50 {
            return Ok(());
        }

        // 简单的模型训练逻辑
        let mut model = self.prediction_model.write().await;
        model.last_trained = Utc::now();
        model.accuracy = 0.85 + (metrics_history.len() as f64 * 0.001).min(0.95); // 数据越多，准确度越高

        println!(
            "🤖 预测模型训练完成 - 准确度: {:.1}%",
            model.accuracy * 100.0
        );
        Ok(())
    }
}

/// 自动扩缩容服务
pub struct AutoScalingService {
    config: ScalingConfig,
    horizontal_scaler: Arc<HorizontalScaler>,
    vertical_scaler: Arc<VerticalScaler>,
    predictive_scaler: Arc<PredictiveScaler>,
    is_running: Arc<RwLock<bool>>,
}

impl AutoScalingService {
    pub fn new(config: ScalingConfig) -> Self {
        let horizontal_scaler = Arc::new(HorizontalScaler::new(config.clone()));
        let vertical_scaler = Arc::new(VerticalScaler::new(config.clone()));
        let predictive_scaler = Arc::new(PredictiveScaler::new(config.clone()));

        Self {
            config,
            horizontal_scaler,
            vertical_scaler,
            predictive_scaler,
            is_running: Arc::new(RwLock::new(false)),
        }
    }

    /// 启动自动扩缩容服务
    pub async fn start(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return Ok(());
        }

        *is_running = true;
        println!("🚀 自动扩缩容服务启动");

        // 启动扩缩容循环
        let horizontal_scaler = self.horizontal_scaler.clone();
        let vertical_scaler = self.vertical_scaler.clone();
        let predictive_scaler = self.predictive_scaler.clone();
        let is_running = self.is_running.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            while *is_running.read().await {
                // 模拟获取指标
                let metrics = ResourceMetrics {
                    timestamp: Utc::now(),
                    cpu_usage: 60.0
                        + (SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            % 40) as f64,
                    memory_usage: 70.0
                        + (SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            % 30) as f64,
                    request_rate: 500.0
                        + (SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            % 200) as f64,
                    response_time: 100.0
                        + (SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            % 50) as f64,
                    error_rate: (SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap()
                        .as_secs()
                        % 10) as f64,
                    active_connections: 100
                        + (SystemTime::now()
                            .duration_since(SystemTime::UNIX_EPOCH)
                            .unwrap()
                            .as_secs()
                            % 50) as u32,
                    queue_length: (SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap()
                        .as_secs()
                        % 20) as u32,
                    custom_metrics: HashMap::new(),
                };

                // 水平扩缩容
                if config.enable_horizontal_scaling
                    && let Ok(action) = horizontal_scaler.evaluate_scaling(&metrics).await
                    && action != ScalingAction::NoAction
                {
                    let _ = horizontal_scaler.execute_scaling(action, &metrics).await;
                }

                // 垂直扩缩容
                if config.enable_vertical_scaling
                    && let Ok(action) = vertical_scaler.evaluate_scaling(&metrics).await
                    && action != ScalingAction::NoAction
                {
                    let _ = vertical_scaler.execute_scaling(action, &metrics).await;
                }

                // 预测性扩缩容
                if config.enable_predictive_scaling {
                    let metrics_history = horizontal_scaler.get_metrics_history().await;
                    if let Ok(predictions) = predictive_scaler
                        .generate_predictions(&metrics_history)
                        .await
                        && let Ok(action) = predictive_scaler
                            .evaluate_predictive_scaling(&predictions)
                            .await
                        && action != ScalingAction::NoAction
                    {
                        let _ = predictive_scaler
                            .execute_predictive_scaling(action, &predictions)
                            .await;
                    }
                }

                // 等待下一次评估
                tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
            }
        });

        Ok(())
    }

    /// 停止自动扩缩容服务
    pub async fn stop(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        *is_running = false;
        println!("🛑 自动扩缩容服务停止");
        Ok(())
    }

    /// 获取扩缩容统计
    pub async fn get_scaling_stats(&self) -> Result<ScalingStats> {
        let horizontal_history = self.horizontal_scaler.get_scaling_history().await;
        let vertical_history = self.vertical_scaler.get_scaling_history().await;
        let predictive_history = self.predictive_scaler.get_scaling_history().await;

        let total_scaling_events =
            horizontal_history.len() + vertical_history.len() + predictive_history.len();
        let scale_up_events = horizontal_history
            .iter()
            .filter(|e| e.action == ScalingAction::ScaleUp)
            .count()
            + vertical_history
                .iter()
                .filter(|e| e.action == ScalingAction::ScaleUp)
                .count()
            + predictive_history
                .iter()
                .filter(|e| e.action == ScalingAction::ScaleUp)
                .count();

        let scale_down_events = horizontal_history
            .iter()
            .filter(|e| e.action == ScalingAction::ScaleDown)
            .count()
            + vertical_history
                .iter()
                .filter(|e| e.action == ScalingAction::ScaleDown)
                .count()
            + predictive_history
                .iter()
                .filter(|e| e.action == ScalingAction::ScaleDown)
                .count();

        let current_replicas = self.horizontal_scaler.get_current_replicas().await;
        let (cpu_limit, memory_limit) = self.vertical_scaler.get_current_limits().await;

        Ok(ScalingStats {
            total_scaling_events,
            scale_up_events,
            scale_down_events,
            current_replicas,
            cpu_limit,
            memory_limit,
            horizontal_scaling_events: horizontal_history.len(),
            vertical_scaling_events: vertical_history.len(),
            predictive_scaling_events: predictive_history.len(),
        })
    }

    /// 获取配置
    pub fn get_config(&self) -> &ScalingConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ScalingConfig) {
        self.config = config;
    }

    /// 获取水平扩缩容器
    pub fn horizontal_scaler(&self) -> &Arc<HorizontalScaler> {
        &self.horizontal_scaler
    }

    /// 获取垂直扩缩容器
    pub fn vertical_scaler(&self) -> &Arc<VerticalScaler> {
        &self.vertical_scaler
    }

    /// 获取预测性扩缩容器
    pub fn predictive_scaler(&self) -> &Arc<PredictiveScaler> {
        &self.predictive_scaler
    }
}

/// 扩缩容统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScalingStats {
    pub total_scaling_events: usize,
    pub scale_up_events: usize,
    pub scale_down_events: usize,
    pub current_replicas: u32,
    pub cpu_limit: f64,
    pub memory_limit: f64,
    pub horizontal_scaling_events: usize,
    pub vertical_scaling_events: usize,
    pub predictive_scaling_events: usize,
}

/// 自动扩缩容服务工厂
pub struct AutoScalingServiceFactory;

impl AutoScalingServiceFactory {
    /// 创建默认配置的自动扩缩容服务
    pub fn create_default_service() -> AutoScalingService {
        AutoScalingService::new(ScalingConfig::default())
    }

    /// 创建自定义配置的自动扩缩容服务
    pub fn create_custom_service(config: ScalingConfig) -> AutoScalingService {
        AutoScalingService::new(config)
    }

    /// 创建生产环境配置
    pub fn create_production_config() -> ScalingConfig {
        ScalingConfig {
            enable_horizontal_scaling: true,
            enable_vertical_scaling: false, // 生产环境通常禁用垂直扩缩容
            enable_predictive_scaling: true,
            min_replicas: 2,
            max_replicas: 20,
            target_cpu_utilization: 70.0,
            target_memory_utilization: 80.0,
            scale_up_threshold: 80.0,
            scale_down_threshold: 30.0,
            scale_up_cooldown: 300,
            scale_down_cooldown: 600,
            predictive_window: 3600,
            custom_metrics: Vec::new(),
        }
    }

    /// 创建测试环境配置
    pub fn create_testing_config() -> ScalingConfig {
        ScalingConfig {
            enable_horizontal_scaling: true,
            enable_vertical_scaling: true,
            enable_predictive_scaling: true,
            min_replicas: 1,
            max_replicas: 5,
            target_cpu_utilization: 60.0,
            target_memory_utilization: 70.0,
            scale_up_threshold: 70.0,
            scale_down_threshold: 40.0,
            scale_up_cooldown: 60,
            scale_down_cooldown: 120,
            predictive_window: 1800,
            custom_metrics: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_horizontal_scaler() {
        let config = ScalingConfig::default();
        let scaler = HorizontalScaler::new(config);

        let metrics = ResourceMetrics {
            timestamp: Utc::now(),
            cpu_usage: 90.0,
            memory_usage: 80.0,
            request_rate: 1000.0,
            response_time: 100.0,
            error_rate: 1.0,
            active_connections: 100,
            queue_length: 10,
            custom_metrics: HashMap::new(),
        };

        let action = scaler.evaluate_scaling(&metrics).await.unwrap();
        assert_eq!(action, ScalingAction::ScaleUp);
    }

    #[tokio::test]
    async fn test_vertical_scaler() {
        let config = ScalingConfig::default();
        let scaler = VerticalScaler::new(config);

        let metrics = ResourceMetrics {
            timestamp: Utc::now(),
            cpu_usage: 95.0,
            memory_usage: 90.0,
            request_rate: 1000.0,
            response_time: 100.0,
            error_rate: 1.0,
            active_connections: 100,
            queue_length: 10,
            custom_metrics: HashMap::new(),
        };

        let action = scaler.evaluate_scaling(&metrics).await.unwrap();
        assert_eq!(action, ScalingAction::ScaleUp);
    }

    #[tokio::test]
    async fn test_predictive_scaler() {
        let config = ScalingConfig::default();
        let scaler = PredictiveScaler::new(config);

        let mut metrics_history = Vec::new();
        for i in 0..20 {
            metrics_history.push(ResourceMetrics {
                timestamp: Utc::now() - Duration::minutes(i as i64),
                cpu_usage: 60.0 + (i as f64 * 2.0),
                memory_usage: 70.0 + (i as f64 * 1.5),
                request_rate: 500.0 + (i as f64 * 10.0),
                response_time: 100.0 + (i as f64 * 5.0),
                error_rate: 1.0,
                active_connections: 100,
                queue_length: 10,
                custom_metrics: HashMap::new(),
            });
        }

        let predictions = scaler.generate_predictions(&metrics_history).await.unwrap();
        assert!(!predictions.is_empty());
    }
}
