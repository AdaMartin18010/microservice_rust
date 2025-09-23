//! 高级微服务架构模式模块
//!
//! 本模块实现了现代化的微服务架构模式，包括：
//! - 领域驱动设计(DDD)
//! - CQRS与事件溯源
//! - Saga模式与分布式事务
//! - 混沌工程与容错设计
//! - 自动扩缩容与弹性设计

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration};
use tokio::sync::{RwLock};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use uuid::Uuid;

/// 错误类型定义
#[derive(Error, Debug)]
pub enum ArchitectureError {
    #[error("领域错误: {0}")]
    DomainError(String),
    
    #[error("命令处理错误: {0}")]
    CommandError(String),
    
    #[error("查询处理错误: {0}")]
    QueryError(String),
    
    #[error("事件处理错误: {0}")]
    EventError(String),
    
    #[error("Saga协调错误: {0}")]
    SagaError(String),
    
    #[error("混沌工程错误: {0}")]
    ChaosError(String),
    
    #[error("扩缩容错误: {0}")]
    ScalingError(String),
    
    #[error("内部错误: {0}")]
    Internal(#[from] anyhow::Error),
}

/// 领域事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainEvent {
    pub id: Uuid,
    pub aggregate_id: String,
    pub event_type: String,
    pub event_data: serde_json::Value,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub version: u64,
}

/// 命令
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Command {
    pub id: Uuid,
    pub command_type: String,
    pub aggregate_id: String,
    pub command_data: serde_json::Value,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 查询
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Query {
    pub id: Uuid,
    pub query_type: String,
    pub query_data: serde_json::Value,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 聚合根
pub trait AggregateRoot {
    type Command;
    type Event;
    type State;
    
    fn handle_command(&mut self, command: Self::Command) -> Result<Vec<Self::Event>, ArchitectureError>;
    fn apply_event(&mut self, event: Self::Event) -> Result<(), ArchitectureError>;
    fn get_state(&self) -> &Self::State;
    fn get_version(&self) -> u64;
}

/// 命令处理器
#[async_trait::async_trait]
pub trait CommandHandler<C> {
    async fn handle(&self, command: C) -> Result<Vec<DomainEvent>, ArchitectureError>;
}

/// 查询处理器
#[async_trait::async_trait]
pub trait QueryHandler<Q, R> {
    async fn handle(&self, query: Q) -> Result<R, ArchitectureError>;
}

/// 事件处理器
#[async_trait::async_trait]
pub trait EventHandler<E> {
    async fn handle(&self, event: E) -> Result<(), ArchitectureError>;
}

/// 事件存储
#[async_trait::async_trait]
pub trait EventStore {
    async fn save_events(&self, aggregate_id: &str, events: Vec<DomainEvent>, expected_version: u64) -> Result<(), ArchitectureError>;
    async fn get_events(&self, aggregate_id: &str, from_version: u64) -> Result<Vec<DomainEvent>, ArchitectureError>;
    async fn get_all_events(&self, from_timestamp: chrono::DateTime<chrono::Utc>) -> Result<Vec<DomainEvent>, ArchitectureError>;
}

/// 内存事件存储实现
pub struct InMemoryEventStore {
    events: Arc<RwLock<HashMap<String, Vec<DomainEvent>>>>,
    event_stream: Arc<RwLock<Vec<DomainEvent>>>,
}

impl InMemoryEventStore {
    pub fn new() -> Self {
        Self {
            events: Arc::new(RwLock::new(HashMap::new())),
            event_stream: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait::async_trait]
impl EventStore for InMemoryEventStore {
    async fn save_events(&self, aggregate_id: &str, events: Vec<DomainEvent>, expected_version: u64) -> Result<(), ArchitectureError> {
        let mut aggregate_events = self.events.write().await;
        let mut event_stream = self.event_stream.write().await;
        
        // 检查版本一致性
        let current_version = aggregate_events.get(aggregate_id)
            .map(|events| events.len() as u64)
            .unwrap_or(0);
        
        if current_version != expected_version {
            return Err(ArchitectureError::DomainError(
                format!("版本冲突: 期望 {}, 实际 {}", expected_version, current_version)
            ));
        }
        
        // 保存事件
        let aggregate_events_list = aggregate_events.entry(aggregate_id.to_string()).or_insert_with(Vec::new);
        aggregate_events_list.extend(events.clone());
        
        // 添加到事件流
        event_stream.extend(events);
        
        Ok(())
    }
    
    async fn get_events(&self, aggregate_id: &str, from_version: u64) -> Result<Vec<DomainEvent>, ArchitectureError> {
        let events = self.events.read().await;
        if let Some(aggregate_events) = events.get(aggregate_id) {
            Ok(aggregate_events.iter()
                .skip(from_version as usize)
                .cloned()
                .collect())
        } else {
            Ok(Vec::new())
        }
    }
    
    async fn get_all_events(&self, from_timestamp: chrono::DateTime<chrono::Utc>) -> Result<Vec<DomainEvent>, ArchitectureError> {
        let events = self.event_stream.read().await;
        Ok(events.iter()
            .filter(|event| event.timestamp >= from_timestamp)
            .cloned()
            .collect())
    }
}

/// 用户聚合根
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserAggregate {
    pub id: String,
    pub name: String,
    pub email: String,
    pub status: UserStatus,
    pub version: u64,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum UserStatus {
    Active,
    Inactive,
    Suspended,
}

/// 用户命令
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UserCommand {
    CreateUser { name: String, email: String },
    UpdateUser { name: Option<String>, email: Option<String> },
    ActivateUser,
    DeactivateUser,
    SuspendUser { reason: String },
}

/// 用户事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UserEvent {
    UserCreated { id: String, name: String, email: String },
    UserUpdated { id: String, name: Option<String>, email: Option<String> },
    UserActivated { id: String },
    UserDeactivated { id: String },
    UserSuspended { id: String, reason: String },
}

impl AggregateRoot for UserAggregate {
    type Command = UserCommand;
    type Event = UserEvent;
    type State = UserAggregate;
    
    fn handle_command(&mut self, command: Self::Command) -> Result<Vec<Self::Event>, ArchitectureError> {
        match command {
            UserCommand::CreateUser { name, email } => {
                if self.id.is_empty() {
                    Ok(vec![UserEvent::UserCreated {
                        id: self.id.clone(),
                        name,
                        email,
                    }])
                } else {
                    Err(ArchitectureError::DomainError("用户已存在".to_string()))
                }
            }
            UserCommand::UpdateUser { name, email } => {
                if self.status == UserStatus::Active {
                    Ok(vec![UserEvent::UserUpdated {
                        id: self.id.clone(),
                        name,
                        email,
                    }])
                } else {
                    Err(ArchitectureError::DomainError("只能更新活跃用户".to_string()))
                }
            }
            UserCommand::ActivateUser => {
                if self.status == UserStatus::Inactive {
                    Ok(vec![UserEvent::UserActivated {
                        id: self.id.clone(),
                    }])
                } else {
                    Err(ArchitectureError::DomainError("只能激活非活跃用户".to_string()))
                }
            }
            UserCommand::DeactivateUser => {
                if self.status == UserStatus::Active {
                    Ok(vec![UserEvent::UserDeactivated {
                        id: self.id.clone(),
                    }])
                } else {
                    Err(ArchitectureError::DomainError("只能停用活跃用户".to_string()))
                }
            }
            UserCommand::SuspendUser { reason } => {
                if self.status == UserStatus::Active {
                    Ok(vec![UserEvent::UserSuspended {
                        id: self.id.clone(),
                        reason,
                    }])
                } else {
                    Err(ArchitectureError::DomainError("只能暂停活跃用户".to_string()))
                }
            }
        }
    }
    
    fn apply_event(&mut self, event: Self::Event) -> Result<(), ArchitectureError> {
        match event {
            UserEvent::UserCreated { id, name, email } => {
                self.id = id;
                self.name = name;
                self.email = email;
                self.status = UserStatus::Active;
                self.created_at = chrono::Utc::now();
                self.updated_at = chrono::Utc::now();
                self.version += 1;
            }
            UserEvent::UserUpdated { id: _, name, email } => {
                if let Some(name) = name {
                    self.name = name;
                }
                if let Some(email) = email {
                    self.email = email;
                }
                self.updated_at = chrono::Utc::now();
                self.version += 1;
            }
            UserEvent::UserActivated { .. } => {
                self.status = UserStatus::Active;
                self.updated_at = chrono::Utc::now();
                self.version += 1;
            }
            UserEvent::UserDeactivated { .. } => {
                self.status = UserStatus::Inactive;
                self.updated_at = chrono::Utc::now();
                self.version += 1;
            }
            UserEvent::UserSuspended { .. } => {
                self.status = UserStatus::Suspended;
                self.updated_at = chrono::Utc::now();
                self.version += 1;
            }
        }
        Ok(())
    }
    
    fn get_state(&self) -> &Self::State {
        self
    }
    
    fn get_version(&self) -> u64 {
        self.version
    }
}

/// 用户命令处理器
pub struct UserCommandHandler {
    event_store: Arc<dyn EventStore + Send + Sync>,
}

impl UserCommandHandler {
    pub fn new(event_store: Arc<dyn EventStore + Send + Sync>) -> Self {
        Self { event_store }
    }
}

#[async_trait::async_trait]
impl CommandHandler<UserCommand> for UserCommandHandler {
    async fn handle(&self, command: UserCommand) -> Result<Vec<DomainEvent>, ArchitectureError> {
        let aggregate_id = match &command {
            UserCommand::CreateUser { .. } => Uuid::new_v4().to_string(),
            _ => return Err(ArchitectureError::CommandError("需要指定聚合ID".to_string())),
        };
        
        // 重建聚合
        let events = self.event_store.get_events(&aggregate_id, 0).await?;
        let mut aggregate = UserAggregate {
            id: aggregate_id.clone(),
            name: String::new(),
            email: String::new(),
            status: UserStatus::Inactive,
            version: 0,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        for event in events {
            if let Ok(user_event) = serde_json::from_value(event.event_data) {
                aggregate.apply_event(user_event)?;
            }
        }
        
        // 处理命令
        let domain_events = aggregate.handle_command(command)?;
        
        // 转换为领域事件
        let domain_events: Vec<DomainEvent> = domain_events.into_iter().map(|event| {
            DomainEvent {
                id: Uuid::new_v4(),
                aggregate_id: aggregate_id.clone(),
                event_type: format!("{:?}", event),
                event_data: serde_json::to_value(event).unwrap(),
                timestamp: chrono::Utc::now(),
                version: aggregate.get_version(),
            }
        }).collect();
        
        // 保存事件
        self.event_store.save_events(&aggregate_id, domain_events.clone(), aggregate.get_version() - domain_events.len() as u64).await?;
        
        Ok(domain_events)
    }
}

/// 用户查询处理器
pub struct UserQueryHandler {
    read_model: Arc<RwLock<HashMap<String, UserAggregate>>>,
}

impl UserQueryHandler {
    pub fn new() -> Self {
        Self {
            read_model: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn update_read_model(&self, event: &DomainEvent) -> Result<(), ArchitectureError> {
        if let Ok(user_event) = serde_json::from_value::<UserEvent>(event.event_data.clone()) {
            let mut read_model = self.read_model.write().await;
            let mut user = read_model.get(&event.aggregate_id).cloned().unwrap_or_else(|| {
                UserAggregate {
                    id: event.aggregate_id.clone(),
                    name: String::new(),
                    email: String::new(),
                    status: UserStatus::Inactive,
                    version: 0,
                    created_at: chrono::Utc::now(),
                    updated_at: chrono::Utc::now(),
                }
            });
            
            user.apply_event(user_event)?;
            read_model.insert(event.aggregate_id.clone(), user);
        }
        Ok(())
    }
}

#[async_trait::async_trait]
impl QueryHandler<GetUserQuery, Option<UserAggregate>> for UserQueryHandler {
    async fn handle(&self, query: GetUserQuery) -> Result<Option<UserAggregate>, ArchitectureError> {
        let read_model = self.read_model.read().await;
        Ok(read_model.get(&query.user_id).cloned())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GetUserQuery {
    pub user_id: String,
}

/// Saga协调器
#[allow(dead_code)]
pub struct SagaCoordinator {
    sagas: Arc<RwLock<HashMap<String, Box<dyn Saga + Send + Sync>>>>,
    event_store: Arc<dyn EventStore + Send + Sync>,
}

#[async_trait::async_trait]
pub trait Saga {
    fn get_id(&self) -> &str;
    fn get_steps(&self) -> &[SagaStep];
    async fn execute(&self) -> Result<(), ArchitectureError>;
    async fn compensate(&self) -> Result<(), ArchitectureError>;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct SagaStep {
    pub id: String,
    pub action: String,
    pub compensation: String,
    pub status: SagaStepStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[allow(dead_code)]
pub enum SagaStepStatus {
    Pending,
    Executing,
    Completed,
    Failed,
    Compensated,
}

impl SagaCoordinator {
    pub fn new(event_store: Arc<dyn EventStore + Send + Sync>) -> Self {
        Self {
            sagas: Arc::new(RwLock::new(HashMap::new())),
            event_store,
        }
    }
    
    pub async fn register_saga(&self, saga: Box<dyn Saga + Send + Sync>) {
        let mut sagas = self.sagas.write().await;
        sagas.insert(saga.get_id().to_string(), saga);
    }
    
    pub async fn execute_saga(&self, saga_id: &str) -> Result<(), ArchitectureError> {
        let sagas = self.sagas.read().await;
        if let Some(saga) = sagas.get(saga_id) {
            saga.execute().await
        } else {
            Err(ArchitectureError::SagaError(format!("Saga {} 未找到", saga_id)))
        }
    }
}

/// 订单Saga
#[allow(dead_code)]
pub struct OrderSaga {
    pub id: String,
    pub order_id: String,
    pub steps: Vec<SagaStep>,
}

impl OrderSaga {
    pub fn new(order_id: String) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            order_id,
            steps: vec![
                SagaStep {
                    id: "reserve_inventory".to_string(),
                    action: "reserve_inventory".to_string(),
                    compensation: "release_inventory".to_string(),
                    status: SagaStepStatus::Pending,
                },
                SagaStep {
                    id: "process_payment".to_string(),
                    action: "process_payment".to_string(),
                    compensation: "refund_payment".to_string(),
                    status: SagaStepStatus::Pending,
                },
                SagaStep {
                    id: "create_shipment".to_string(),
                    action: "create_shipment".to_string(),
                    compensation: "cancel_shipment".to_string(),
                    status: SagaStepStatus::Pending,
                },
            ],
        }
    }
}

#[async_trait::async_trait]
impl Saga for OrderSaga {
    fn get_id(&self) -> &str {
        &self.id
    }
    
    fn get_steps(&self) -> &[SagaStep] {
        &self.steps
    }
    
    async fn execute(&self) -> Result<(), ArchitectureError> {
        for step in &self.steps {
            tracing::info!("执行Saga步骤: {}", step.action);
            
            // 模拟步骤执行
            match step.action.as_str() {
                "reserve_inventory" => {
                    // 模拟库存预留
                    tokio::time::sleep(Duration::from_millis(100)).await;
                    tracing::info!("库存预留成功");
                }
                "process_payment" => {
                    // 模拟支付处理
                    tokio::time::sleep(Duration::from_millis(200)).await;
                    tracing::info!("支付处理成功");
                }
                "create_shipment" => {
                    // 模拟创建发货
                    tokio::time::sleep(Duration::from_millis(150)).await;
                    tracing::info!("发货创建成功");
                }
                _ => return Err(ArchitectureError::SagaError(format!("未知的Saga步骤: {}", step.action))),
            }
        }
        
        Ok(())
    }
    
    async fn compensate(&self) -> Result<(), ArchitectureError> {
        // 反向执行补偿操作
        for step in self.steps.iter().rev() {
            tracing::info!("执行补偿步骤: {}", step.compensation);
            
            match step.compensation.as_str() {
                "release_inventory" => {
                    tokio::time::sleep(Duration::from_millis(50)).await;
                    tracing::info!("库存释放成功");
                }
                "refund_payment" => {
                    tokio::time::sleep(Duration::from_millis(100)).await;
                    tracing::info!("支付退款成功");
                }
                "cancel_shipment" => {
                    tokio::time::sleep(Duration::from_millis(75)).await;
                    tracing::info!("发货取消成功");
                }
                _ => return Err(ArchitectureError::SagaError(format!("未知的补偿步骤: {}", step.compensation))),
            }
        }
        
        Ok(())
    }
}

/// 混沌工程
#[allow(dead_code)]
pub struct ChaosEngineering {
    fault_injectors: Arc<RwLock<Vec<Box<dyn FaultInjector + Send + Sync>>>>,
    experiments: Arc<RwLock<HashMap<String, ChaosExperiment>>>,
}

#[async_trait::async_trait]
pub trait FaultInjector {
    fn get_name(&self) -> &str;
    fn get_fault_type(&self) -> FaultType;
    async fn inject_fault(&self) -> Result<(), ArchitectureError>;
    async fn remove_fault(&self) -> Result<(), ArchitectureError>;
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum FaultType {
    Latency,
    Error,
    ResourceExhaustion,
    NetworkPartition,
    ServiceUnavailable,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosExperiment {
    pub id: String,
    pub name: String,
    pub description: String,
    pub fault_type: FaultType,
    pub duration: Duration,
    pub severity: Severity,
    pub status: ExperimentStatus,
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
    pub results: Option<ExperimentResults>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Severity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ExperimentStatus {
    Planned,
    Running,
    Completed,
    Failed,
    Cancelled,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExperimentResults {
    pub success_rate: f64,
    pub error_rate: f64,
    pub average_response_time: f64,
    pub system_stability: SystemStability,
    pub observations: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SystemStability {
    Stable,
    Degraded,
    Unstable,
    Failed,
}

impl ChaosEngineering {
    pub fn new() -> Self {
        Self {
            fault_injectors: Arc::new(RwLock::new(Vec::new())),
            experiments: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn register_fault_injector(&self, injector: Box<dyn FaultInjector + Send + Sync>) {
        let mut injectors = self.fault_injectors.write().await;
        injectors.push(injector);
    }
    
    pub async fn run_experiment(&self, experiment: ChaosExperiment) -> Result<ExperimentResults, ArchitectureError> {
        let experiment_id = experiment.id.clone();
        let mut experiments = self.experiments.write().await;
        experiments.insert(experiment_id.clone(), experiment);
        
        // 查找合适的故障注入器
        let injectors = self.fault_injectors.read().await;
        let injector = injectors.iter()
            .find(|injector| injector.get_fault_type() == experiments[&experiment_id].fault_type)
            .ok_or_else(|| ArchitectureError::ChaosError("未找到合适的故障注入器".to_string()))?;
        
        // 开始实验
        {
            let exp = experiments.get_mut(&experiment_id).unwrap();
            exp.status = ExperimentStatus::Running;
            exp.start_time = Some(chrono::Utc::now());
        }
        
        // 注入故障
        injector.inject_fault().await?;
        
        // 等待实验持续时间
        tokio::time::sleep(experiments[&experiment_id].duration).await;
        
        // 移除故障
        injector.remove_fault().await?;
        
        // 生成实验结果
        let results = ExperimentResults {
            success_rate: 0.95, // 模拟数据
            error_rate: 0.05,
            average_response_time: 150.0,
            system_stability: SystemStability::Stable,
            observations: vec![
                "系统在故障期间保持稳定".to_string(),
                "错误率略有上升但可接受".to_string(),
                "响应时间增加但未超阈值".to_string(),
            ],
        };
        
        // 更新实验状态
        {
            let exp = experiments.get_mut(&experiment_id).unwrap();
            exp.status = ExperimentStatus::Completed;
            exp.end_time = Some(chrono::Utc::now());
            exp.results = Some(results.clone());
        }
        
        Ok(results)
    }
}

/// 延迟故障注入器
#[allow(dead_code)]
pub struct LatencyFaultInjector {
    pub name: String,
    pub latency: Duration,
}

#[async_trait::async_trait]
impl FaultInjector for LatencyFaultInjector {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_fault_type(&self) -> FaultType {
        FaultType::Latency
    }
    
    async fn inject_fault(&self) -> Result<(), ArchitectureError> {
        tracing::info!("注入延迟故障: {}ms", self.latency.as_millis());
        // 实际实现中，这里会修改网络或服务配置
        Ok(())
    }
    
    async fn remove_fault(&self) -> Result<(), ArchitectureError> {
        tracing::info!("移除延迟故障");
        // 实际实现中，这里会恢复网络或服务配置
        Ok(())
    }
}

/// 自动扩缩容
pub struct AutoScaling {
    scalers: Arc<RwLock<Vec<Box<dyn Scaler + Send + Sync>>>>,
    metrics: Arc<RwLock<HashMap<String, MetricValue>>>,
    scaling_events: Arc<RwLock<Vec<ScalingEvent>>>,
}

#[async_trait::async_trait]
pub trait Scaler {
    fn get_name(&self) -> &str;
    fn get_scaling_type(&self) -> ScalingType;
    async fn should_scale(&self, metrics: &HashMap<String, MetricValue>) -> Result<ScalingAction, ArchitectureError>;
    async fn scale(&self, action: ScalingAction) -> Result<(), ArchitectureError>;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScalingType {
    Horizontal,
    Vertical,
    Predictive,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScalingAction {
    pub action_type: ScalingActionType,
    pub target_count: Option<u32>,
    pub target_cpu: Option<f64>,
    pub target_memory: Option<f64>,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ScalingActionType {
    ScaleUp,
    ScaleDown,
    NoAction,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScalingEvent {
    pub id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub action: ScalingAction,
    pub success: bool,
    pub error_message: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricValue {
    pub value: f64,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub unit: String,
}

impl AutoScaling {
    pub fn new() -> Self {
        Self {
            scalers: Arc::new(RwLock::new(Vec::new())),
            metrics: Arc::new(RwLock::new(HashMap::new())),
            scaling_events: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    pub async fn register_scaler(&self, scaler: Box<dyn Scaler + Send + Sync>) {
        let mut scalers = self.scalers.write().await;
        scalers.push(scaler);
    }
    
    pub async fn update_metric(&self, name: String, value: MetricValue) {
        let mut metrics = self.metrics.write().await;
        metrics.insert(name, value);
    }
    
    pub async fn evaluate_scaling(&self) -> Result<(), ArchitectureError> {
        let scalers = self.scalers.read().await;
        let metrics = self.metrics.read().await;
        
        for scaler in scalers.iter() {
            match scaler.should_scale(&metrics).await {
                Ok(action) => {
                    if !matches!(action.action_type, ScalingActionType::NoAction) {
                        let event_id = Uuid::new_v4().to_string();
                        let timestamp = chrono::Utc::now();
                        
                        match scaler.scale(action.clone()).await {
                            Ok(_) => {
                                let event = ScalingEvent {
                                    id: event_id,
                                    timestamp,
                                    action,
                                    success: true,
                                    error_message: None,
                                };
                                
                                let mut events = self.scaling_events.write().await;
                                events.push(event);
                                
                                tracing::info!("扩缩容操作成功");
                            }
                            Err(e) => {
                                let event = ScalingEvent {
                                    id: event_id,
                                    timestamp,
                                    action,
                                    success: false,
                                    error_message: Some(e.to_string()),
                                };
                                
                                let mut events = self.scaling_events.write().await;
                                events.push(event);
                                
                                tracing::error!("扩缩容操作失败: {}", e);
                            }
                        }
                    }
                }
                Err(e) => {
                    tracing::error!("扩缩容评估失败: {}", e);
                }
            }
        }
        
        Ok(())
    }
}

/// CPU扩缩容器
pub struct CpuScaler {
    pub name: String,
    pub scale_up_threshold: f64,
    pub scale_down_threshold: f64,
    pub min_instances: u32,
    pub max_instances: u32,
}

#[async_trait::async_trait]
impl Scaler for CpuScaler {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_scaling_type(&self) -> ScalingType {
        ScalingType::Horizontal
    }
    
    async fn should_scale(&self, metrics: &HashMap<String, MetricValue>) -> Result<ScalingAction, ArchitectureError> {
        if let Some(cpu_metric) = metrics.get("cpu_usage") {
            let current_instances = metrics.get("instance_count")
                .map(|m| m.value as u32)
                .unwrap_or(1);
            
            if cpu_metric.value > self.scale_up_threshold && current_instances < self.max_instances {
                Ok(ScalingAction {
                    action_type: ScalingActionType::ScaleUp,
                    target_count: Some(current_instances + 1),
                    target_cpu: None,
                    target_memory: None,
                    reason: format!("CPU使用率 {}% 超过阈值 {}%", cpu_metric.value, self.scale_up_threshold),
                })
            } else if cpu_metric.value < self.scale_down_threshold && current_instances > self.min_instances {
                Ok(ScalingAction {
                    action_type: ScalingActionType::ScaleDown,
                    target_count: Some(current_instances - 1),
                    target_cpu: None,
                    target_memory: None,
                    reason: format!("CPU使用率 {}% 低于阈值 {}%", cpu_metric.value, self.scale_down_threshold),
                })
            } else {
                Ok(ScalingAction {
                    action_type: ScalingActionType::NoAction,
                    target_count: None,
                    target_cpu: None,
                    target_memory: None,
                    reason: "CPU使用率在正常范围内".to_string(),
                })
            }
        } else {
            Ok(ScalingAction {
                action_type: ScalingActionType::NoAction,
                target_count: None,
                target_cpu: None,
                target_memory: None,
                reason: "缺少CPU使用率指标".to_string(),
            })
        }
    }
    
    async fn scale(&self, action: ScalingAction) -> Result<(), ArchitectureError> {
        match action.action_type {
            ScalingActionType::ScaleUp => {
                tracing::info!("扩展实例到: {:?}", action.target_count);
                // 实际实现中，这里会调用Kubernetes API或其他编排系统
                tokio::time::sleep(Duration::from_millis(500)).await;
            }
            ScalingActionType::ScaleDown => {
                tracing::info!("缩减实例到: {:?}", action.target_count);
                // 实际实现中，这里会调用Kubernetes API或其他编排系统
                tokio::time::sleep(Duration::from_millis(300)).await;
            }
            ScalingActionType::NoAction => {
                // 无需操作
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_user_aggregate() {
        let mut user = UserAggregate {
            id: "user-1".to_string(),
            name: String::new(),
            email: String::new(),
            status: UserStatus::Inactive,
            version: 0,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        let command = UserCommand::CreateUser {
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        };
        
        let events = user.handle_command(command).unwrap();
        assert_eq!(events.len(), 1);
        
        user.apply_event(events[0].clone()).unwrap();
        assert_eq!(user.name, "Alice");
        assert_eq!(user.email, "alice@example.com");
        assert_eq!(user.status, UserStatus::Active);
    }
    
    #[tokio::test]
    async fn test_event_store() {
        let event_store = InMemoryEventStore::new();
        let aggregate_id = "test-aggregate";
        
        let events = vec![
            DomainEvent {
                id: Uuid::new_v4(),
                aggregate_id: aggregate_id.to_string(),
                event_type: "TestEvent".to_string(),
                event_data: serde_json::json!({"message": "test"}),
                timestamp: chrono::Utc::now(),
                version: 1,
            },
        ];
        
        event_store.save_events(aggregate_id, events.clone(), 0).await.unwrap();
        
        let retrieved_events = event_store.get_events(aggregate_id, 0).await.unwrap();
        assert_eq!(retrieved_events.len(), 1);
        assert_eq!(retrieved_events[0].event_type, "TestEvent");
    }
    
    #[tokio::test]
    async fn test_saga_execution() {
        let saga = OrderSaga::new("order-123".to_string());
        
        let result = saga.execute().await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_chaos_experiment() {
        let chaos = ChaosEngineering::new();
        let injector = LatencyFaultInjector {
            name: "test-injector".to_string(),
            latency: Duration::from_millis(100),
        };
        
        chaos.register_fault_injector(Box::new(injector)).await;
        
        let experiment = ChaosExperiment {
            id: "test-experiment".to_string(),
            name: "延迟测试".to_string(),
            description: "测试系统对延迟的响应".to_string(),
            fault_type: FaultType::Latency,
            duration: Duration::from_millis(100),
            severity: Severity::Low,
            status: ExperimentStatus::Planned,
            start_time: None,
            end_time: None,
            results: None,
        };
        
        let results = chaos.run_experiment(experiment).await.unwrap();
        assert!(results.success_rate > 0.0);
    }
    
    #[tokio::test]
    async fn test_auto_scaling() {
        let auto_scaling = AutoScaling::new();
        let scaler = CpuScaler {
            name: "cpu-scaler".to_string(),
            scale_up_threshold: 80.0,
            scale_down_threshold: 20.0,
            min_instances: 1,
            max_instances: 10,
        };
        
        auto_scaling.register_scaler(Box::new(scaler)).await;
        
        // 模拟高CPU使用率
        auto_scaling.update_metric("cpu_usage".to_string(), MetricValue {
            value: 85.0,
            timestamp: chrono::Utc::now(),
            unit: "percent".to_string(),
        }).await;
        
        auto_scaling.update_metric("instance_count".to_string(), MetricValue {
            value: 2.0,
            timestamp: chrono::Utc::now(),
            unit: "count".to_string(),
        }).await;
        
        auto_scaling.evaluate_scaling().await.unwrap();
        
        let events = auto_scaling.scaling_events.read().await;
        assert!(!events.is_empty());
    }
}
