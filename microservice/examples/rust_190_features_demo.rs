//! Rust 1.90 新特性演示
//!
//! 本示例展示了Rust 1.90版本中引入的新特性在微服务开发中的应用
//! 包括：异步trait、泛型关联类型(GAT)、类型别名实现特性(TAIT)等

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Rust 1.90 新特性：稳定的异步trait
/// 不再需要async-trait宏，可以直接定义异步trait
trait AsyncService {
    async fn process_request(&self, request: ServiceRequest) -> Result<ServiceResponse>;
    async fn health_check(&self) -> Result<HealthStatus>;
}

/// 泛型关联类型(GAT)示例
/// 允许在trait中定义关联类型的泛型参数
trait AsyncIterator {
    type Item<'a>
    where
        Self: 'a;
    type Future<'a>: Future<Output = Option<Self::Item<'a>>>
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Self::Future<'a>;
}

/// 类型别名实现特性(TAIT)示例
/// 简化复杂类型的定义
#[allow(dead_code)]
type ServiceResult<T> = Pin<Box<dyn Future<Output = Result<T, ServiceError>> + Send>>;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ServiceRequest {
    pub id: String,
    pub data: String,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ServiceResponse {
    pub id: String,
    pub result: String,
    pub status: ResponseStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub enum ResponseStatus {
    Success,
    Error(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct HealthStatus {
    pub service: String,
    pub status: String,
    pub timestamp: u64,
}

#[derive(Debug, thiserror::Error)]
#[allow(dead_code)]
pub enum ServiceError {
    #[error("处理请求失败: {0}")]
    ProcessingError(String),
    #[error("服务不可用: {0}")]
    ServiceUnavailable(String),
    #[error("网络错误: {0}")]
    NetworkError(String),
}

/// 服务类型枚举
#[derive(Debug)]
#[allow(dead_code)]
pub enum ServiceType {
    User(UserService),
    Order(OrderService),
}

/// 用户服务实现
#[derive(Debug)]
#[allow(dead_code)]
pub struct UserService {
    users: Arc<RwLock<HashMap<String, User>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
}

impl UserService {
    pub fn new() -> Self {
        let mut users = HashMap::new();
        users.insert(
            "1".to_string(),
            User {
                id: "1".to_string(),
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
            },
        );
        users.insert(
            "2".to_string(),
            User {
                id: "2".to_string(),
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
            },
        );

        Self {
            users: Arc::new(RwLock::new(users)),
        }
    }
}

/// 实现异步trait（Rust 1.90新特性）
impl AsyncService for UserService {
    async fn process_request(&self, request: ServiceRequest) -> Result<ServiceResponse> {
        println!("处理用户服务请求: {:?}", request);

        // 模拟异步处理
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        let users = self.users.read().await;
        let user = users.get(&request.id);

        match user {
            Some(user) => Ok(ServiceResponse {
                id: request.id,
                result: serde_json::to_string(user)?,
                status: ResponseStatus::Success,
            }),
            None => Ok(ServiceResponse {
                id: request.id,
                result: "用户未找到".to_string(),
                status: ResponseStatus::Error("用户不存在".to_string()),
            }),
        }
    }

    async fn health_check(&self) -> Result<HealthStatus> {
        Ok(HealthStatus {
            service: "user-service".to_string(),
            status: "healthy".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
        })
    }
}

/// 订单服务实现
#[derive(Debug)]
pub struct OrderService {
    orders: Arc<RwLock<HashMap<String, Order>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: String,
    pub user_id: String,
    pub items: Vec<OrderItem>,
    pub total: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: String,
    pub quantity: u32,
    pub price: f64,
}

impl OrderService {
    pub fn new() -> Self {
        let mut orders = HashMap::new();
        orders.insert(
            "1".to_string(),
            Order {
                id: "1".to_string(),
                user_id: "1".to_string(),
                items: vec![OrderItem {
                    product_id: "p1".to_string(),
                    quantity: 2,
                    price: 10.0,
                }],
                total: 20.0,
            },
        );

        Self {
            orders: Arc::new(RwLock::new(orders)),
        }
    }
}

impl AsyncService for OrderService {
    async fn process_request(&self, request: ServiceRequest) -> Result<ServiceResponse> {
        println!("处理订单服务请求: {:?}", request);

        // 模拟异步处理
        tokio::time::sleep(tokio::time::Duration::from_millis(150)).await;

        let orders = self.orders.read().await;
        let order = orders.get(&request.id);

        match order {
            Some(order) => Ok(ServiceResponse {
                id: request.id,
                result: serde_json::to_string(order)?,
                status: ResponseStatus::Success,
            }),
            None => Ok(ServiceResponse {
                id: request.id,
                result: "订单未找到".to_string(),
                status: ResponseStatus::Error("订单不存在".to_string()),
            }),
        }
    }

    async fn health_check(&self) -> Result<HealthStatus> {
        Ok(HealthStatus {
            service: "order-service".to_string(),
            status: "healthy".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
        })
    }
}

impl AsyncService for ServiceType {
    async fn process_request(&self, request: ServiceRequest) -> Result<ServiceResponse> {
        match self {
            ServiceType::User(service) => service.process_request(request).await,
            ServiceType::Order(service) => service.process_request(request).await,
        }
    }

    async fn health_check(&self) -> Result<HealthStatus> {
        match self {
            ServiceType::User(service) => service.health_check().await,
            ServiceType::Order(service) => service.health_check().await,
        }
    }
}

/// 异步迭代器实现（使用GAT）
pub struct ServiceRequestStream {
    requests: Vec<ServiceRequest>,
    index: usize,
}

impl ServiceRequestStream {
    pub fn new(requests: Vec<ServiceRequest>) -> Self {
        Self { requests, index: 0 }
    }
}

impl AsyncIterator for ServiceRequestStream {
    type Item<'a> = &'a ServiceRequest;
    type Future<'a> = Pin<Box<dyn Future<Output = Option<&'a ServiceRequest>> + 'a>>;

    fn next<'a>(&'a mut self) -> Self::Future<'a> {
        Box::pin(async move {
            if self.index < self.requests.len() {
                let item = &self.requests[self.index];
                self.index += 1;
                Some(item)
            } else {
                None
            }
        })
    }
}

/// 服务管理器
#[derive(Clone)]
pub struct ServiceManager {
    services: Arc<RwLock<HashMap<String, ServiceType>>>,
}

impl ServiceManager {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn register_service(&self, name: String, service: ServiceType) {
        let mut services = self.services.write().await;
        services.insert(name, service);
    }

    pub async fn process_request(
        &self,
        service_name: &str,
        request: ServiceRequest,
    ) -> Result<ServiceResponse> {
        let services = self.services.read().await;
        if let Some(service) = services.get(service_name) {
            service.process_request(request).await
        } else {
            Err(ServiceError::ServiceUnavailable(format!("服务 {} 未找到", service_name)).into())
        }
    }

    pub async fn health_check_all(&self) -> Result<Vec<HealthStatus>> {
        let services = self.services.read().await;
        let mut results = Vec::new();

        for (name, service) in services.iter() {
            match service.health_check().await {
                Ok(status) => results.push(status),
                Err(e) => {
                    results.push(HealthStatus {
                        service: name.clone(),
                        status: format!("unhealthy: {}", e),
                        timestamp: std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap_or_default()
                            .as_secs(),
                    });
                }
            }
        }

        Ok(results)
    }
}

/// 使用TAIT的异步函数
#[allow(dead_code)]
async fn process_service_result<T>(result: ServiceResult<T>) -> Result<T> {
    match result.await {
        Ok(value) => Ok(value),
        Err(e) => Err(anyhow::Error::from(e)),
    }
}

/// 主函数演示Rust 1.90新特性
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.90 新特性演示");
    println!("================================");

    // 创建服务管理器
    let manager = ServiceManager::new();

    // 注册服务
    manager
        .register_service("user".to_string(), ServiceType::User(UserService::new()))
        .await;

    manager
        .register_service("order".to_string(), ServiceType::Order(OrderService::new()))
        .await;

    // 演示异步trait使用
    println!("\n📡 演示异步trait使用:");
    let user_request = ServiceRequest {
        id: "1".to_string(),
        data: "get_user".to_string(),
        metadata: HashMap::new(),
    };

    let response = manager.process_request("user", user_request).await?;
    println!("用户服务响应: {:?}", response);

    let order_request = ServiceRequest {
        id: "1".to_string(),
        data: "get_order".to_string(),
        metadata: HashMap::new(),
    };

    let response = manager.process_request("order", order_request).await?;
    println!("订单服务响应: {:?}", response);

    // 演示异步迭代器（GAT）
    println!("\n🔄 演示异步迭代器（GAT）:");
    let requests = vec![
        ServiceRequest {
            id: "1".to_string(),
            data: "request1".to_string(),
            metadata: HashMap::new(),
        },
        ServiceRequest {
            id: "2".to_string(),
            data: "request2".to_string(),
            metadata: HashMap::new(),
        },
    ];

    let mut stream = ServiceRequestStream::new(requests);
    while let Some(request) = stream.next().await {
        println!("处理请求: {:?}", request);
    }

    // 演示健康检查
    println!("\n🏥 演示健康检查:");
    let health_statuses = manager.health_check_all().await?;
    for status in health_statuses {
        println!("服务健康状态: {:?}", status);
    }

    // 演示并发处理
    println!("\n⚡ 演示并发处理:");
    let handles: Vec<_> = (1..=5)
        .map(|i| {
            let manager = Arc::new(manager.clone());
            tokio::spawn(async move {
                let request = ServiceRequest {
                    id: i.to_string(),
                    data: format!("concurrent_request_{}", i),
                    metadata: HashMap::new(),
                };

                let service_name = if i % 2 == 0 { "user" } else { "order" };
                match manager.process_request(service_name, request).await {
                    Ok(response) => println!("并发请求 {} 成功: {:?}", i, response),
                    Err(e) => println!("并发请求 {} 失败: {}", i, e),
                }
            })
        })
        .collect();

    // 等待所有并发任务完成
    for handle in handles {
        handle.await?;
    }

    println!("\n✅ Rust 1.90 新特性演示完成！");
    println!("主要特性包括:");
    println!("- 稳定的异步trait，无需async-trait宏");
    println!("- 泛型关联类型(GAT)支持");
    println!("- 类型别名实现特性(TAIT)");
    println!("- 改进的异步编程体验");
    println!("- 更好的类型推断和错误处理");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_user_service() {
        let service = UserService::new();
        let request = ServiceRequest {
            id: "1".to_string(),
            data: "test".to_string(),
            metadata: HashMap::new(),
        };

        let response = service.process_request(request).await.unwrap();
        assert_eq!(response.status, ResponseStatus::Success);
    }

    #[tokio::test]
    async fn test_order_service() {
        let service = OrderService::new();
        let request = ServiceRequest {
            id: "1".to_string(),
            data: "test".to_string(),
            metadata: HashMap::new(),
        };

        let response = service.process_request(request).await.unwrap();
        assert_eq!(response.status, ResponseStatus::Success);
    }

    #[tokio::test]
    async fn test_service_manager() {
        let manager = ServiceManager::new();
        manager
            .register_service("test".to_string(), Box::new(UserService::new()))
            .await;

        let request = ServiceRequest {
            id: "1".to_string(),
            data: "test".to_string(),
            metadata: HashMap::new(),
        };

        let response = manager.process_request("test", request).await.unwrap();
        assert_eq!(response.status, ResponseStatus::Success);
    }
}
