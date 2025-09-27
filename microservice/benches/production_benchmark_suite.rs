//! 生产级性能基准测试套件
//! 
//! 本测试套件模拟真实生产环境的负载模式，包括：
//! - 不同并发级别的性能测试
//! - 内存使用情况分析
//! - 延迟分布统计
//! - 错误率监控
//! - 资源利用率分析

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::hint::black_box;
use std::time::Duration;
use tokio::runtime::Runtime;
use std::sync::Arc;
use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use std::time::{SystemTime};

// 测试数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkRequest {
    pub id: Uuid,
    pub user_id: Uuid,
    pub data: Vec<u8>,
    pub timestamp: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResponse {
    pub id: Uuid,
    pub status: String,
    pub processing_time: Duration,
    pub memory_usage: u64,
}

// 模拟微服务组件
pub struct MockUserService {
    cache: Arc<tokio::sync::RwLock<HashMap<Uuid, String>>>,
}

impl MockUserService {
    pub fn new() -> Self {
        Self {
            cache: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
        }
    }

    pub async fn get_user(&self, user_id: Uuid) -> Result<String, String> {
        // 模拟数据库查询延迟
        tokio::time::sleep(Duration::from_millis(1)).await;
        
        let cache = self.cache.read().await;
        if let Some(user) = cache.get(&user_id) {
            return Ok(user.clone());
        }
        drop(cache);

        // 模拟数据库查询
        let user_data = format!("user_{}", user_id);
        let mut cache = self.cache.write().await;
        cache.insert(user_id, user_data.clone());
        Ok(user_data)
    }

    pub async fn create_user(&self, user_id: Uuid, name: String) -> Result<String, String> {
        // 模拟数据库写入延迟
        tokio::time::sleep(Duration::from_millis(2)).await;
        
        let mut cache = self.cache.write().await;
        cache.insert(user_id, name.clone());
        Ok(name)
    }
}

pub struct MockOrderService {
    orders: Arc<tokio::sync::RwLock<HashMap<Uuid, BenchmarkRequest>>>,
}

impl MockOrderService {
    pub fn new() -> Self {
        Self {
            orders: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
        }
    }

    pub async fn create_order(&self, request: BenchmarkRequest) -> Result<BenchmarkResponse, String> {
        let start_time = SystemTime::now();
        
        // 模拟订单处理逻辑
        tokio::time::sleep(Duration::from_millis(5)).await;
        
        // 模拟数据验证
        if request.data.is_empty() {
            return Err("Invalid order data".to_string());
        }

        // 存储订单
        let mut orders = self.orders.write().await;
        orders.insert(request.id, request.clone());
        drop(orders);

        let processing_time = start_time.elapsed().unwrap_or_default();
        let memory_usage = self.get_memory_usage().await;

        Ok(BenchmarkResponse {
            id: request.id,
            status: "created".to_string(),
            processing_time,
            memory_usage,
        })
    }

    pub async fn get_order(&self, order_id: Uuid) -> Result<Option<BenchmarkRequest>, String> {
        // 模拟数据库查询延迟
        tokio::time::sleep(Duration::from_millis(1)).await;
        
        let orders = self.orders.read().await;
        Ok(orders.get(&order_id).cloned())
    }

    async fn get_memory_usage(&self) -> u64 {
        // 模拟内存使用统计
        let orders = self.orders.read().await;
        orders.len() as u64 * 1024 // 假设每个订单占用1KB
    }
}

pub struct MockPaymentService {
    payments: Arc<tokio::sync::RwLock<HashMap<Uuid, f64>>>,
    failure_rate: f64,
}

impl MockPaymentService {
    pub fn new(failure_rate: f64) -> Self {
        Self {
            payments: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
            failure_rate,
        }
    }

    pub async fn process_payment(&self, order_id: Uuid, amount: f64) -> Result<String, String> {
        let start_time = SystemTime::now();
        
        // 模拟支付处理延迟
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        // 模拟支付失败
        if rand::random::<f64>() < self.failure_rate {
            return Err("Payment failed".to_string());
        }

        // 存储支付记录
        let mut payments = self.payments.write().await;
        payments.insert(order_id, amount);
        drop(payments);

        let processing_time = start_time.elapsed().unwrap_or_default();
        Ok(format!("Payment processed in {:?}", processing_time))
    }
}

// 基准测试函数
fn benchmark_user_service_read(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let user_service = MockUserService::new();
    
    // 预热
    rt.block_on(async {
        let user_id = Uuid::new_v4();
        let _ = user_service.create_user(user_id, "test_user".to_string()).await;
    });

    let mut group = c.benchmark_group("user_service_read");
    group.throughput(Throughput::Elements(1));
    
    for concurrency in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_reads", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    rt.block_on(async {
                        let user_id = Uuid::new_v4();
                        let _ = user_service.create_user(user_id, "benchmark_user".to_string()).await;
                        
                        let tasks: Vec<_> = (0..concurrency)
                            .map(|_| {
                                let service = &user_service;
                                let user_id = Uuid::new_v4();
                                async move {
                                    service.get_user(user_id).await
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

fn benchmark_user_service_write(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let user_service = MockUserService::new();

    let mut group = c.benchmark_group("user_service_write");
    group.throughput(Throughput::Elements(1));
    
    for concurrency in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_writes", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    rt.block_on(async {
                        let tasks: Vec<_> = (0..concurrency)
                            .map(|i| {
                                let service = &user_service;
                                let user_id = Uuid::new_v4();
                                let name = format!("user_{}", i);
                                async move {
                                    service.create_user(user_id, name).await
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

fn benchmark_order_service(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let order_service = MockOrderService::new();

    let mut group = c.benchmark_group("order_service");
    group.throughput(Throughput::Elements(1));
    
    for concurrency in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_orders", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    rt.block_on(async {
                        let tasks: Vec<_> = (0..concurrency)
                            .map(|_i| {
                                let service = &order_service;
                                let request = BenchmarkRequest {
                                    id: Uuid::new_v4(),
                                    user_id: Uuid::new_v4(),
                                    data: vec![0u8; 1024], // 1KB数据
                                    timestamp: SystemTime::now(),
                                };
                                async move {
                                    service.create_order(request).await
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

fn benchmark_payment_service(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("payment_service");
    group.throughput(Throughput::Elements(1));
    
    for failure_rate in [0.0, 0.01, 0.05, 0.1].iter() {
        let payment_service = MockPaymentService::new(*failure_rate);
        
        group.bench_with_input(
            BenchmarkId::new("payment_processing", format!("failure_rate_{}", failure_rate)),
            failure_rate,
            |b, &_failure_rate| {
                b.iter(|| {
                    rt.block_on(async {
                        let tasks: Vec<_> = (0..100)
                            .map(|i| {
                                let service = &payment_service;
                                let order_id = Uuid::new_v4();
                                let amount = 100.0 + i as f64;
                                async move {
                                    service.process_payment(order_id, amount).await
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

fn benchmark_memory_usage(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let order_service = MockOrderService::new();

    let mut group = c.benchmark_group("memory_usage");
    group.throughput(Throughput::Elements(1));
    
    for data_size in [1024, 10240, 102400, 1048576].iter() { // 1KB to 1MB
        group.bench_with_input(
            BenchmarkId::new("data_size", data_size),
            data_size,
            |b, &data_size| {
                b.iter(|| {
                    rt.block_on(async {
                        let tasks: Vec<_> = (0..100)
                            .map(|_i| {
                                let service = &order_service;
                                let request = BenchmarkRequest {
                                    id: Uuid::new_v4(),
                                    user_id: Uuid::new_v4(),
                                    data: vec![0u8; data_size],
                                    timestamp: SystemTime::now(),
                                };
                                async move {
                                    service.create_order(request).await
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

fn benchmark_latency_distribution(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let user_service = MockUserService::new();
    let order_service = MockOrderService::new();
    let payment_service = MockPaymentService::new(0.01);

    let mut group = c.benchmark_group("latency_distribution");
    group.throughput(Throughput::Elements(1));
    group.measurement_time(Duration::from_secs(30)); // 延长测试时间以获得更好的统计
    
    group.bench_function("end_to_end_latency", |b| {
        b.iter(|| {
            rt.block_on(async {
                let user_id = Uuid::new_v4();
                
                // 创建用户
                let _ = user_service.create_user(user_id, "test_user".to_string()).await;
                
                // 创建订单
                let order_request = BenchmarkRequest {
                    id: Uuid::new_v4(),
                    user_id,
                    data: vec![0u8; 1024],
                    timestamp: SystemTime::now(),
                };
                let order_result = order_service.create_order(order_request).await;
                
                // 处理支付
                if let Ok(order_response) = order_result {
                    let _ = payment_service.process_payment(order_response.id, 100.0).await;
                }
                
                black_box(())
            })
        })
    });
    
    group.finish();
}

fn benchmark_error_handling(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let payment_service = MockPaymentService::new(0.1); // 10% 失败率

    let mut group = c.benchmark_group("error_handling");
    group.throughput(Throughput::Elements(1));
    
    group.bench_function("payment_with_retry", |b| {
        b.iter(|| {
            rt.block_on(async {
                let order_id = Uuid::new_v4();
                let mut attempts = 0;
                let max_attempts = 3;
                
                loop {
                    attempts += 1;
                    match payment_service.process_payment(order_id, 100.0).await {
                        Ok(result) => {
                            black_box(result);
                            break;
                        }
                        Err(_) if attempts < max_attempts => {
                            // 模拟重试延迟
                            tokio::time::sleep(Duration::from_millis(100)).await;
                            continue;
                        }
                        Err(e) => {
                            black_box(e);
                            break;
                        }
                    }
                }
            })
        })
    });
    
    group.finish();
}

fn benchmark_concurrent_services(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let user_service = MockUserService::new();
    let order_service = MockOrderService::new();
    let payment_service = MockPaymentService::new(0.01);

    let mut group = c.benchmark_group("concurrent_services");
    group.throughput(Throughput::Elements(1));
    
    for concurrency in [10, 50, 100, 500].iter() {
        group.bench_with_input(
            BenchmarkId::new("mixed_workload", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    rt.block_on(async {
                        let tasks: Vec<_> = (0..concurrency)
                            .map(|i| {
                                let user_service = &user_service;
                                let order_service = &order_service;
                                let payment_service = &payment_service;
                                
                                async move {
                                    let user_id = Uuid::new_v4();
                                    
                                    // 创建用户
                                    let _ = user_service.create_user(user_id, format!("user_{}", i)).await;
                                    
                                    // 创建订单
                                    let order_request = BenchmarkRequest {
                                        id: Uuid::new_v4(),
                                        user_id,
                                        data: vec![0u8; 1024],
                                        timestamp: SystemTime::now(),
                                    };
                                    let order_result = order_service.create_order(order_request).await;
                                    
                                    // 处理支付
                                    if let Ok(order_response) = order_result {
                                        let _ = payment_service.process_payment(order_response.id, 100.0).await;
                                    }
                                    
                                    black_box(())
                                }
                            })
                            .collect();
                        
                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }
    group.finish();
}

// 基准测试组配置
criterion_group!(
    benches,
    benchmark_user_service_read,
    benchmark_user_service_write,
    benchmark_order_service,
    benchmark_payment_service,
    benchmark_memory_usage,
    benchmark_latency_distribution,
    benchmark_error_handling,
    benchmark_concurrent_services
);

criterion_main!(benches);

// 性能分析工具
pub struct PerformanceAnalyzer {
    metrics: Arc<tokio::sync::RwLock<HashMap<String, Vec<f64>>>>,
}

impl PerformanceAnalyzer {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(tokio::sync::RwLock::new(HashMap::new())),
        }
    }

    pub async fn record_metric(&self, name: String, value: f64) {
        let mut metrics = self.metrics.write().await;
        metrics.entry(name).or_insert_with(Vec::new).push(value);
    }

    pub async fn get_statistics(&self, name: &str) -> Option<PerformanceStats> {
        let metrics = self.metrics.read().await;
        if let Some(values) = metrics.get(name) {
            if values.is_empty() {
                return None;
            }

            let mut sorted_values = values.clone();
            sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());

            let count = values.len();
            let sum: f64 = values.iter().sum();
            let mean = sum / count as f64;
            
            let median = if count % 2 == 0 {
                (sorted_values[count / 2 - 1] + sorted_values[count / 2]) / 2.0
            } else {
                sorted_values[count / 2]
            };

            let p95_index = (count as f64 * 0.95) as usize;
            let p99_index = (count as f64 * 0.99) as usize;
            
            let p95 = sorted_values[p95_index.min(count - 1)];
            let p99 = sorted_values[p99_index.min(count - 1)];

            let variance: f64 = values.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / count as f64;
            let std_dev = variance.sqrt();

            Some(PerformanceStats {
                count,
                mean,
                median,
                p95,
                p99,
                std_dev,
                min: sorted_values[0],
                max: sorted_values[count - 1],
            })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct PerformanceStats {
    pub count: usize,
    pub mean: f64,
    pub median: f64,
    pub p95: f64,
    pub p99: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
}

impl std::fmt::Display for PerformanceStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, 
            "Count: {}, Mean: {:.2}, Median: {:.2}, P95: {:.2}, P99: {:.2}, StdDev: {:.2}, Min: {:.2}, Max: {:.2}",
            self.count, self.mean, self.median, self.p95, self.p99, self.std_dev, self.min, self.max
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_performance_analyzer() {
        let analyzer = PerformanceAnalyzer::new();
        
        // 记录一些测试数据
        for i in 1..=100 {
            analyzer.record_metric("test_metric".to_string(), i as f64).await;
        }
        
        let stats = analyzer.get_statistics("test_metric").await.unwrap();
        assert_eq!(stats.count, 100);
        assert_eq!(stats.mean, 50.5);
        assert_eq!(stats.median, 50.5);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 100.0);
    }

    #[tokio::test]
    async fn test_mock_services() {
        let user_service = MockUserService::new();
        let order_service = MockOrderService::new();
        let payment_service = MockPaymentService::new(0.0);
        
        // 测试用户服务
        let user_id = Uuid::new_v4();
        let result = user_service.create_user(user_id, "test_user".to_string()).await;
        assert!(result.is_ok());
        
        // 测试订单服务
        let order_request = BenchmarkRequest {
            id: Uuid::new_v4(),
            user_id,
            data: vec![0u8; 1024],
            timestamp: SystemTime::now(),
        };
        let order_result = order_service.create_order(order_request.clone()).await;
        assert!(order_result.is_ok());
        
        // 测试支付服务
        let payment_result = payment_service.process_payment(order_request.id, 100.0).await;
        assert!(payment_result.is_ok());
    }
}