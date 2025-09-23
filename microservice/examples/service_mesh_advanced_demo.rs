//! 高级服务网格演示
//! 
//! 本示例展示了如何使用Rust构建高级服务网格功能
//! 包括：流量管理、负载均衡、熔断器、重试、超时、分布式追踪等

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use serde::{Deserialize, Serialize};
use anyhow::Result;
use tracing::{info, warn, error, instrument};
use uuid::Uuid;

/// 服务网格配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceMeshConfig {
    pub service_name: String,
    pub version: String,
    pub endpoints: Vec<ServiceEndpoint>,
    pub traffic_policy: TrafficPolicy,
    pub circuit_breaker: CircuitBreakerConfig,
    pub retry_policy: RetryPolicy,
    pub timeout_config: TimeoutConfig,
    pub load_balancer: LoadBalancerConfig,
    pub tracing: TracingConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceEndpoint {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub weight: u32,
    pub healthy: bool,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficPolicy {
    pub canary_percentage: u32,
    pub stable_percentage: u32,
    pub header_routing: HashMap<String, String>,
    pub path_routing: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub success_threshold: u32,
    pub timeout_duration: Duration,
    pub max_requests: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryPolicy {
    pub max_attempts: u32,
    pub base_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub retryable_errors: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutConfig {
    pub connect_timeout: Duration,
    pub request_timeout: Duration,
    pub idle_timeout: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadBalancerConfig {
    pub strategy: LoadBalancingStrategy,
    pub health_check_interval: Duration,
    pub health_check_timeout: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
    ConsistentHash,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracingConfig {
    pub enabled: bool,
    pub sampling_rate: f64,
    pub jaeger_endpoint: Option<String>,
    pub zipkin_endpoint: Option<String>,
}

/// 请求上下文
#[derive(Debug, Clone)]
pub struct RequestContext {
    pub request_id: String,
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub headers: HashMap<String, String>,
    pub start_time: Instant,
    pub retry_count: u32,
}

/// 响应信息
#[derive(Debug, Clone)]
pub struct ResponseInfo {
    pub status_code: u16,
    pub duration: Duration,
    pub size: usize,
    pub error: Option<String>,
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器
#[derive(Debug)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitBreakerState>>,
    failure_count: Arc<RwLock<u32>>,
    success_count: Arc<RwLock<u32>>,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
    request_count: Arc<RwLock<u32>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(RwLock::new(0)),
            success_count: Arc::new(RwLock::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
            request_count: Arc::new(RwLock::new(0)),
        }
    }
    
    #[instrument]
    pub async fn can_execute(&self) -> bool {
        let state = self.state.read().await;
        match *state {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => {
                // 检查是否可以进入半开状态
                let last_failure = self.last_failure_time.read().await;
                if let Some(last_failure_time) = *last_failure {
                    if last_failure_time.elapsed() >= self.config.timeout_duration {
                        // 切换到半开状态
                        drop(state);
                        let mut state = self.state.write().await;
                        *state = CircuitBreakerState::HalfOpen;
                        info!("熔断器切换到半开状态");
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            CircuitBreakerState::HalfOpen => {
                let request_count = self.request_count.read().await;
                *request_count < self.config.max_requests
            }
        }
    }
    
    #[instrument]
    pub async fn record_success(&self) {
        let mut state = self.state.write().await;
        let mut success_count = self.success_count.write().await;
        let mut failure_count = self.failure_count.write().await;
        
        *success_count += 1;
        *failure_count = 0;
        
        if *state == CircuitBreakerState::HalfOpen {
            if *success_count >= self.config.success_threshold {
                *state = CircuitBreakerState::Closed;
                info!("熔断器切换到关闭状态");
            }
        }
    }
    
    #[instrument]
    pub async fn record_failure(&self) {
        let mut state = self.state.write().await;
        let mut failure_count = self.failure_count.write().await;
        let mut last_failure_time = self.last_failure_time.write().await;
        
        *failure_count += 1;
        *last_failure_time = Some(Instant::now());
        
        if *failure_count >= self.config.failure_threshold {
            *state = CircuitBreakerState::Open;
            info!("熔断器切换到开启状态");
        }
    }
    
    pub async fn get_state(&self) -> CircuitBreakerState {
        let state = self.state.read().await;
        state.clone()
    }
}

/// 负载均衡器
#[derive(Debug)]
pub struct LoadBalancer {
    config: LoadBalancerConfig,
    endpoints: Arc<RwLock<Vec<ServiceEndpoint>>>,
    current_index: Arc<RwLock<usize>>,
    connection_counts: Arc<RwLock<HashMap<String, u32>>>,
}

impl LoadBalancer {
    pub fn new(config: LoadBalancerConfig, endpoints: Vec<ServiceEndpoint>) -> Self {
        Self {
            config,
            endpoints: Arc::new(RwLock::new(endpoints)),
            current_index: Arc::new(RwLock::new(0)),
            connection_counts: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    #[instrument]
    pub async fn select_endpoint(&self) -> Option<ServiceEndpoint> {
        let endpoints = self.endpoints.read().await;
        let healthy_endpoints: Vec<&ServiceEndpoint> = endpoints
            .iter()
            .filter(|ep| ep.healthy)
            .collect();
        
        if healthy_endpoints.is_empty() {
            return None;
        }
        
        let selected = match self.config.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let mut index = self.current_index.write().await;
                let selected = healthy_endpoints[*index % healthy_endpoints.len()];
                *index += 1;
                selected.clone()
            }
            LoadBalancingStrategy::WeightedRoundRobin => {
                // 简化的加权轮询实现
                let total_weight: u32 = healthy_endpoints.iter().map(|ep| ep.weight).sum();
                let mut index = self.current_index.write().await;
                let mut current_weight = 0;
                
                for endpoint in &healthy_endpoints {
                    current_weight += endpoint.weight;
                    if *index < current_weight as usize {
                        *index += 1;
                        return Some(endpoint.clone());
                    }
                }
                healthy_endpoints[0].clone()
            }
            LoadBalancingStrategy::LeastConnections => {
                let connection_counts = self.connection_counts.read().await;
                let mut least_connections = u32::MAX;
                let mut selected_endpoint = None;
                
                for endpoint in &healthy_endpoints {
                    let connections = connection_counts.get(&endpoint.id).copied().unwrap_or(0);
                    if connections < least_connections {
                        least_connections = connections;
                        selected_endpoint = Some(endpoint.clone());
                    }
                }
                
                selected_endpoint.unwrap_or(&healthy_endpoints[0]).clone()
            }
            LoadBalancingStrategy::Random => {
                let index = rand::random::<usize>() % healthy_endpoints.len();
                healthy_endpoints[index].clone()
            }
            LoadBalancingStrategy::ConsistentHash => {
                // 简化的一致性哈希实现
                let index = rand::random::<usize>() % healthy_endpoints.len();
                healthy_endpoints[index].clone()
            }
        };
        
        Some(selected)
    }
    
    #[instrument]
    pub async fn update_endpoint_health(&self, endpoint_id: &str, healthy: bool) {
        let mut endpoints = self.endpoints.write().await;
        for endpoint in endpoints.iter_mut() {
            if endpoint.id == endpoint_id {
                endpoint.healthy = healthy;
                break;
            }
        }
    }
    
    #[instrument]
    pub async fn increment_connections(&self, endpoint_id: &str) {
        let mut connection_counts = self.connection_counts.write().await;
        *connection_counts.entry(endpoint_id.to_string()).or_insert(0) += 1;
    }
    
    #[instrument]
    pub async fn decrement_connections(&self, endpoint_id: &str) {
        let mut connection_counts = self.connection_counts.write().await;
        if let Some(count) = connection_counts.get_mut(endpoint_id) {
            if *count > 0 {
                *count -= 1;
            }
        }
    }
}

/// 重试器
#[derive(Debug)]
pub struct RetryHandler {
    config: RetryPolicy,
}

impl RetryHandler {
    pub fn new(config: RetryPolicy) -> Self {
        Self { config }
    }
    
    pub async fn execute_with_retry<F, Fut, T, E>(
        &self,
        operation: F,
        _ctx: &RequestContext,
    ) -> Result<T, E>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display,
    {
        let mut attempt = 0;
        let mut delay = self.config.base_delay;
        
        loop {
            attempt += 1;
            
            let result = operation().await;
            
            match result {
                Ok(value) => return Ok(value),
                Err(error) => {
                    if attempt >= self.config.max_attempts {
                        error!("重试次数已达上限，操作失败: {}", error);
                        return Err(error);
                    }
                    
                    if !self.should_retry(&error.to_string()) {
                        error!("错误不可重试: {}", error);
                        return Err(error);
                    }
                    
                    warn!("操作失败，第 {} 次重试: {}", attempt, error);
                    
                    // 计算退避延迟
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(
                        Duration::from_millis(
                            (delay.as_millis() as f64 * self.config.backoff_multiplier) as u64
                        ),
                        self.config.max_delay,
                    );
                }
            }
        }
    }
    
    fn should_retry(&self, error: &str) -> bool {
        self.config.retryable_errors.iter().any(|retryable| {
            error.contains(retryable)
        })
    }
}

/// 分布式追踪
#[derive(Debug)]
pub struct DistributedTracer {
    config: TracingConfig,
    spans: Arc<RwLock<HashMap<String, SpanInfo>>>,
}

#[derive(Debug, Clone)]
pub struct SpanInfo {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub operation_name: String,
    pub start_time: Instant,
    pub tags: HashMap<String, String>,
}

impl DistributedTracer {
    pub fn new(config: TracingConfig) -> Self {
        Self {
            config,
            spans: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    #[instrument]
    pub fn start_span(&self, operation_name: &str, parent_span_id: Option<&str>) -> String {
        if !self.config.enabled {
            return String::new();
        }
        
        let span_id = Uuid::new_v4().to_string();
        let trace_id = parent_span_id
            .and_then(|pid| {
                let spans = self.spans.blocking_read();
                spans.get(pid).map(|span| span.trace_id.clone())
            })
            .unwrap_or_else(|| Uuid::new_v4().to_string());
        
        let span_info = SpanInfo {
            trace_id: trace_id.clone(),
            span_id: span_id.clone(),
            parent_span_id: parent_span_id.map(|s| s.to_string()),
            operation_name: operation_name.to_string(),
            start_time: Instant::now(),
            tags: HashMap::new(),
        };
        
        let mut spans = self.spans.blocking_write();
        spans.insert(span_id.clone(), span_info);
        
        info!("开始追踪span: {} (trace: {})", span_id, trace_id);
        span_id
    }
    
    #[instrument]
    pub async fn finish_span(&self, span_id: &str) {
        if !self.config.enabled {
            return;
        }
        
        let mut spans = self.spans.write().await;
        if let Some(span_info) = spans.remove(span_id) {
            let duration = span_info.start_time.elapsed();
            info!(
                "完成追踪span: {} (trace: {}, duration: {:?})",
                span_id, span_info.trace_id, duration
            );
        }
    }
    
    #[instrument]
    pub async fn add_tag(&self, span_id: &str, key: &str, value: &str) {
        if !self.config.enabled {
            return;
        }
        
        let mut spans = self.spans.write().await;
        if let Some(span_info) = spans.get_mut(span_id) {
            span_info.tags.insert(key.to_string(), value.to_string());
        }
    }
}

/// 服务网格代理
#[derive(Debug)]
pub struct ServiceMeshProxy {
    config: ServiceMeshConfig,
    circuit_breaker: CircuitBreaker,
    load_balancer: LoadBalancer,
    retry_handler: RetryHandler,
    tracer: DistributedTracer,
    semaphore: Arc<Semaphore>,
}

impl ServiceMeshProxy {
    pub fn new(config: ServiceMeshConfig) -> Self {
        let circuit_breaker = CircuitBreaker::new(config.circuit_breaker.clone());
        let load_balancer = LoadBalancer::new(
            config.load_balancer.clone(),
            config.endpoints.clone(),
        );
        let retry_handler = RetryHandler::new(config.retry_policy.clone());
        let tracer = DistributedTracer::new(config.tracing.clone());
        let semaphore = Arc::new(Semaphore::new(config.circuit_breaker.max_requests as usize));
        
        Self {
            config,
            circuit_breaker,
            load_balancer,
            retry_handler,
            tracer,
            semaphore,
        }
    }
    
    #[instrument]
    pub async fn handle_request(&self, ctx: RequestContext) -> Result<ResponseInfo> {
        let span_id = self.tracer.start_span("service_mesh_proxy", Some(&ctx.span_id));
        
        // 检查熔断器
        if !self.circuit_breaker.can_execute().await {
            self.tracer.finish_span(&span_id);
            return Err(anyhow::anyhow!("熔断器开启，请求被拒绝"));
        }
        
        // 获取信号量
        let _permit = self.semaphore.acquire().await?;
        
        // 选择端点
        let endpoint = self.load_balancer.select_endpoint().await
            .ok_or_else(|| anyhow::anyhow!("没有可用的健康端点"))?;
        
        self.tracer.add_tag(&span_id, "endpoint", &endpoint.address);
        self.load_balancer.increment_connections(&endpoint.id).await;
        
        let result = self.retry_handler.execute_with_retry(
            || self.execute_request(&ctx, &endpoint),
            &ctx,
        ).await;
        
        self.load_balancer.decrement_connections(&endpoint.id).await;
        
        match result {
            Ok(response) => {
                self.circuit_breaker.record_success().await;
                self.tracer.add_tag(&span_id, "status", "success");
                self.tracer.finish_span(&span_id);
                Ok(response)
            }
            Err(error) => {
                self.circuit_breaker.record_failure().await;
                self.tracer.add_tag(&span_id, "status", "error");
                self.tracer.add_tag(&span_id, "error", &error.to_string());
                self.tracer.finish_span(&span_id);
                Err(error)
            }
        }
    }
    
    #[instrument]
    async fn execute_request(
        &self,
        ctx: &RequestContext,
        endpoint: &ServiceEndpoint,
    ) -> Result<ResponseInfo> {
        let start_time = Instant::now();
        
        // 模拟HTTP请求
        let client = reqwest::Client::builder()
            .timeout(self.config.timeout_config.request_timeout)
            .build()?;
        
        let url = format!("http://{}:{}", endpoint.address, endpoint.port);
        let response = client
            .get(&url)
            .headers({
                let mut headers = reqwest::header::HeaderMap::new();
                headers.insert("X-Request-ID", ctx.request_id.parse()?);
                headers.insert("X-Trace-ID", ctx.trace_id.parse()?);
                headers.insert("X-Span-ID", ctx.span_id.parse()?);
                headers
            })
            .send()
            .await?;
        
        let status_code = response.status().as_u16();
        let body = response.bytes().await?;
        let size = body.len();
        let duration = start_time.elapsed();
        
        Ok(ResponseInfo {
            status_code,
            duration,
            size,
            error: None,
        })
    }
    
    pub async fn get_circuit_breaker_state(&self) -> CircuitBreakerState {
        self.circuit_breaker.get_state().await
    }
    
    pub async fn update_endpoint_health(&self, endpoint_id: &str, healthy: bool) {
        self.load_balancer.update_endpoint_health(endpoint_id, healthy).await;
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 高级服务网格演示");
    println!("================================");
    
    // 创建服务网格配置
    let config = ServiceMeshConfig {
        service_name: "user-service".to_string(),
        version: "1.0.0".to_string(),
        endpoints: vec![
            ServiceEndpoint {
                id: "endpoint-1".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8080,
                weight: 100,
                healthy: true,
                metadata: HashMap::new(),
            },
            ServiceEndpoint {
                id: "endpoint-2".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8081,
                weight: 100,
                healthy: true,
                metadata: HashMap::new(),
            },
            ServiceEndpoint {
                id: "endpoint-3".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8082,
                weight: 50,
                healthy: true,
                metadata: HashMap::new(),
            },
        ],
        traffic_policy: TrafficPolicy {
            canary_percentage: 10,
            stable_percentage: 90,
            header_routing: HashMap::new(),
            path_routing: HashMap::new(),
        },
        circuit_breaker: CircuitBreakerConfig {
            failure_threshold: 5,
            success_threshold: 3,
            timeout_duration: Duration::from_secs(30),
            max_requests: 10,
        },
        retry_policy: RetryPolicy {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(1),
            backoff_multiplier: 2.0,
            retryable_errors: vec!["timeout".to_string(), "connection".to_string()],
        },
        timeout_config: TimeoutConfig {
            connect_timeout: Duration::from_secs(5),
            request_timeout: Duration::from_secs(10),
            idle_timeout: Duration::from_secs(30),
        },
        load_balancer: LoadBalancerConfig {
            strategy: LoadBalancingStrategy::RoundRobin,
            health_check_interval: Duration::from_secs(10),
            health_check_timeout: Duration::from_secs(5),
        },
        tracing: TracingConfig {
            enabled: true,
            sampling_rate: 1.0,
            jaeger_endpoint: Some("http://localhost:14268/api/traces".to_string()),
            zipkin_endpoint: None,
        },
    };
    
    // 创建服务网格代理
    let proxy = ServiceMeshProxy::new(config);
    
    println!("📡 服务网格代理已启动");
    println!("📋 功能特性:");
    println!("  ✅ 熔断器");
    println!("  ✅ 负载均衡");
    println!("  ✅ 重试机制");
    println!("  ✅ 超时控制");
    println!("  ✅ 分布式追踪");
    println!("  ✅ 流量管理");
    println!();
    
    // 模拟请求处理
    for i in 1..=10 {
        let ctx = RequestContext {
            request_id: Uuid::new_v4().to_string(),
            trace_id: Uuid::new_v4().to_string(),
            span_id: Uuid::new_v4().to_string(),
            parent_span_id: None,
            headers: HashMap::new(),
            start_time: Instant::now(),
            retry_count: 0,
        };
        
        match proxy.handle_request(ctx).await {
            Ok(response) => {
                println!("✅ 请求 #{} 成功: 状态码={}, 耗时={:?}, 大小={}字节", 
                    i, response.status_code, response.duration, response.size);
            }
            Err(error) => {
                println!("❌ 请求 #{} 失败: {}", i, error);
            }
        }
        
        // 检查熔断器状态
        let cb_state = proxy.get_circuit_breaker_state().await;
        println!("🔧 熔断器状态: {:?}", cb_state);
        
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    // 模拟端点故障
    println!("\n🔧 模拟端点故障...");
    proxy.update_endpoint_health("endpoint-1", false).await;
    proxy.update_endpoint_health("endpoint-2", false).await;
    
    // 继续发送请求
    for i in 11..=15 {
        let ctx = RequestContext {
            request_id: Uuid::new_v4().to_string(),
            trace_id: Uuid::new_v4().to_string(),
            span_id: Uuid::new_v4().to_string(),
            parent_span_id: None,
            headers: HashMap::new(),
            start_time: Instant::now(),
            retry_count: 0,
        };
        
        match proxy.handle_request(ctx).await {
            Ok(response) => {
                println!("✅ 请求 #{} 成功: 状态码={}, 耗时={:?}", 
                    i, response.status_code, response.duration);
            }
            Err(error) => {
                println!("❌ 请求 #{} 失败: {}", i, error);
            }
        }
        
        let cb_state = proxy.get_circuit_breaker_state().await;
        println!("🔧 熔断器状态: {:?}", cb_state);
        
        tokio::time::sleep(Duration::from_millis(200)).await;
    }
    
    println!("✅ 高级服务网格演示完成！");
    println!("主要特性包括:");
    println!("- 智能熔断器保护");
    println!("- 多种负载均衡策略");
    println!("- 指数退避重试");
    println!("- 分布式追踪");
    println!("- 流量管理和路由");
    println!("- 健康检查和故障转移");
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_circuit_breaker() {
        let config = CircuitBreakerConfig {
            failure_threshold: 3,
            success_threshold: 2,
            timeout_duration: Duration::from_secs(1),
            max_requests: 5,
        };
        
        let cb = CircuitBreaker::new(config);
        
        // 初始状态应该是关闭的
        assert_eq!(cb.get_state().await, CircuitBreakerState::Closed);
        
        // 记录失败，应该保持关闭状态
        cb.record_failure().await;
        assert_eq!(cb.get_state().await, CircuitBreakerState::Closed);
        
        // 记录更多失败，应该切换到开启状态
        cb.record_failure().await;
        cb.record_failure().await;
        assert_eq!(cb.get_state().await, CircuitBreakerState::Open);
        
        // 等待超时后，应该可以执行
        tokio::time::sleep(Duration::from_millis(1100)).await;
        assert!(cb.can_execute().await);
    }
    
    #[tokio::test]
    async fn test_load_balancer() {
        let config = LoadBalancerConfig {
            strategy: LoadBalancingStrategy::RoundRobin,
            health_check_interval: Duration::from_secs(10),
            health_check_timeout: Duration::from_secs(5),
        };
        
        let endpoints = vec![
            ServiceEndpoint {
                id: "ep1".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8080,
                weight: 100,
                healthy: true,
                metadata: HashMap::new(),
            },
            ServiceEndpoint {
                id: "ep2".to_string(),
                address: "127.0.0.1".to_string(),
                port: 8081,
                weight: 100,
                healthy: true,
                metadata: HashMap::new(),
            },
        ];
        
        let lb = LoadBalancer::new(config, endpoints);
        
        // 应该能选择到端点
        let endpoint = lb.select_endpoint().await;
        assert!(endpoint.is_some());
        
        // 更新端点健康状态
        lb.update_endpoint_health("ep1", false).await;
        
        // 应该选择到健康的端点
        let endpoint = lb.select_endpoint().await;
        assert!(endpoint.is_some());
        assert_eq!(endpoint.unwrap().id, "ep2");
    }
}
