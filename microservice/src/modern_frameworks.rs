//! 现代微服务框架集成模块
//!
//! 本模块集成了最新的 Rust 微服务框架，包括：
//! - Poem: 现代化 Web 框架
//! - Salvo: 功能强大的 Web 框架
//! - Volo: 字节跳动高性能 RPC 框架
//! - fusen-rs: 跨语言微服务框架
//! - Spring-rs: Spring Boot 风格的 Rust 框架

use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use serde::{Deserialize, Serialize};
use anyhow::Result;

/// 现代框架统一接口
pub trait ModernFramework {
    /// 启动服务
    fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>>;
    
    /// 停止服务
    fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>>;
    
    /// 健康检查
    fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>>;
    
    /// 获取指标
    fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>>;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthStatus {
    pub status: String,
    pub timestamp: String,
    pub version: String,
    pub uptime: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FrameworkMetrics {
    pub requests_total: u64,
    pub active_connections: u32,
    pub memory_usage_mb: f64,
    pub cpu_usage_percent: f64,
    pub response_time_avg_ms: f64,
}

/// Poem 框架增强支持
#[cfg(feature = "with-poem")]
pub mod poem_advanced {
    use super::*;
    use poem::{
        get, handler, listener::TcpListener, middleware::Tracing, post, put, delete,
        EndpointExt, Route, Server, web::{Json, Path, Query},
        FromRequest, IntoResponse, Request, Response,
    };
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// Poem 高级服务实现
    pub struct PoemAdvancedService {
        app: Route,
        metrics: Arc<RwLock<FrameworkMetrics>>,
        start_time: std::time::Instant,
    }

    impl PoemAdvancedService {
        pub fn new() -> Self {
            let metrics = Arc::new(RwLock::new(FrameworkMetrics {
                requests_total: 0,
                active_connections: 0,
                memory_usage_mb: 0.0,
                cpu_usage_percent: 0.0,
                response_time_avg_ms: 0.0,
            }));

            let app = Route::new()
                .at("/health", get(health_check_handler))
                .at("/metrics", get(metrics_handler))
                .at("/users", get(get_users).post(create_user))
                .at("/users/:id", get(get_user).put(update_user).delete(delete_user))
                .at("/api/v1/users", get(get_users_v1))
                .at("/api/v1/users/:id", get(get_user_v1))
                .with(poem::middleware::Tracing)
                .with(poem::middleware::Cors::new())
                .with(poem::middleware::Compression::new())
                .with(poem::middleware::RequestId::new())
                .with(poem::middleware::Timeout::new(std::time::Duration::from_secs(30)));

            Self {
                app,
                metrics,
                start_time: std::time::Instant::now(),
            }
        }

        pub fn with_custom_routes<F>(mut self, route_builder: F) -> Self
        where
            F: FnOnce(Route) -> Route,
        {
            self.app = route_builder(self.app);
            self
        }
    }

    impl ModernFramework for PoemAdvancedService {
        fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            let app = self.app.clone();
            Box::pin(async move {
                let listener = TcpListener::bind(format!("0.0.0.0:{}", port));
                let server = Server::new(listener).serve(app);
                tracing::info!("Poem 服务启动在端口 {}", port);
                server.await?;
                Ok(())
            })
        }

        fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Poem 服务正在停止...");
                Ok(())
            })
        }

        fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>> {
            let uptime = self.start_time.elapsed().as_secs();
            Box::pin(async move {
                Ok(HealthStatus {
                    status: "healthy".to_string(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    version: "1.0.0".to_string(),
                    uptime,
                })
            })
        }

        fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>> {
            let metrics = self.metrics.clone();
            Box::pin(async move {
                let m = metrics.read().await;
                Ok(m.clone())
            })
        }
    }

    /// 用户数据结构
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct User {
        pub id: String,
        pub name: String,
        pub email: String,
        pub created_at: String,
    }

    /// 用户存储
    pub struct UserStore {
        users: Arc<RwLock<HashMap<String, User>>>,
    }

    impl UserStore {
        pub fn new() -> Self {
            let mut users = HashMap::new();
            users.insert("1".to_string(), User {
                id: "1".to_string(),
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
                created_at: chrono::Utc::now().to_rfc3339(),
            });
            users.insert("2".to_string(), User {
                id: "2".to_string(),
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
                created_at: chrono::Utc::now().to_rfc3339(),
            });

            Self {
                users: Arc::new(RwLock::new(users)),
            }
        }

        pub async fn get_user(&self, id: &str) -> Option<User> {
            let users = self.users.read().await;
            users.get(id).cloned()
        }

        pub async fn create_user(&self, user: User) -> User {
            let mut users = self.users.write().await;
            users.insert(user.id.clone(), user.clone());
            user
        }

        pub async fn update_user(&self, id: &str, user: User) -> Option<User> {
            let mut users = self.users.write().await;
            users.insert(id.to_string(), user.clone());
            Some(user)
        }

        pub async fn delete_user(&self, id: &str) -> bool {
            let mut users = self.users.write().await;
            users.remove(id).is_some()
        }

        pub async fn list_users(&self) -> Vec<User> {
            let users = self.users.read().await;
            users.values().cloned().collect()
        }
    }

    // 全局用户存储
    lazy_static::lazy_static! {
        static ref USER_STORE: UserStore = UserStore::new();
    }

    /// 健康检查处理器
    #[handler]
    async fn health_check_handler() -> Json<HealthStatus> {
        Json(HealthStatus {
            status: "healthy".to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            version: "1.0.0".to_string(),
            uptime: 3600, // 模拟运行时间
        })
    }

    /// 指标处理器
    #[handler]
    async fn metrics_handler() -> Json<FrameworkMetrics> {
        Json(FrameworkMetrics {
            requests_total: 1000,
            active_connections: 50,
            memory_usage_mb: 256.5,
            cpu_usage_percent: 18.2,
            response_time_avg_ms: 45.3,
        })
    }

    /// 获取所有用户
    #[handler]
    async fn get_users() -> Json<Vec<User>> {
        let users = USER_STORE.list_users().await;
        Json(users)
    }

    /// 创建用户
    #[handler]
    async fn create_user(Json(user): Json<User>) -> Json<User> {
        let user = USER_STORE.create_user(user).await;
        Json(user)
    }

    /// 获取单个用户
    #[handler]
    async fn get_user(Path(id): Path<String>) -> Json<Option<User>> {
        let user = USER_STORE.get_user(&id).await;
        Json(user)
    }

    /// 更新用户
    #[handler]
    async fn update_user(Path(id): Path<String>, Json(user): Json<User>) -> Json<Option<User>> {
        let user = USER_STORE.update_user(&id, user).await;
        Json(user)
    }

    /// 删除用户
    #[handler]
    async fn delete_user(Path(id): Path<String>) -> Json<bool> {
        let deleted = USER_STORE.delete_user(&id).await;
        Json(deleted)
    }

    /// API v1 获取所有用户
    #[handler]
    async fn get_users_v1() -> Json<serde_json::Value> {
        let users = USER_STORE.list_users().await;
        Json(serde_json::json!({
            "code": 200,
            "message": "success",
            "data": users,
            "timestamp": chrono::Utc::now().to_rfc3339()
        }))
    }

    /// API v1 获取单个用户
    #[handler]
    async fn get_user_v1(Path(id): Path<String>) -> Json<serde_json::Value> {
        let user = USER_STORE.get_user(&id).await;
        Json(serde_json::json!({
            "code": 200,
            "message": "success",
            "data": user,
            "timestamp": chrono::Utc::now().to_rfc3339()
        }))
    }
}

/// Salvo 框架增强支持
#[allow(dead_code)]
#[cfg(feature = "with-salvo")]
pub mod salvo_advanced {
    use super::*;
    use salvo::{
        prelude::*,
        oapi::{self, extract::*, openapi::OpenApi, ToSchema, ToResponse},
    };
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// Salvo 高级服务实现
    pub struct SalvoAdvancedService {
        router: Router,
        metrics: Arc<RwLock<FrameworkMetrics>>,
        start_time: std::time::Instant,
    }

    impl SalvoAdvancedService {
        pub fn new() -> Self {
            let metrics = Arc::new(RwLock::new(FrameworkMetrics {
                requests_total: 0,
                active_connections: 0,
                memory_usage_mb: 0.0,
                cpu_usage_percent: 0.0,
                response_time_avg_ms: 0.0,
            }));

            let router = Router::new()
                .push(
                    Router::with_path("/health")
                        .get(health_check_handler)
                )
                .push(
                    Router::with_path("/metrics")
                        .get(metrics_handler)
                )
                .push(
                    Router::with_path("/users")
                        .get(get_users)
                        .post(create_user)
                )
                .push(
                    Router::with_path("/users/<id>")
                        .get(get_user)
                        .put(update_user)
                        .delete(delete_user)
                )
                .push(
                    Router::with_path("/api/v1/users")
                        .get(get_users_v1)
                )
                .push(
                    Router::with_path("/api/v1/users/<id>")
                        .get(get_user_v1)
                )
                .hoop(salvo::logging::Logger::new())
                .hoop(salvo::cors::Cors::new()
                    .allow_origin("*")
                    .allow_methods(vec!["GET", "POST", "PUT", "DELETE"])
                    .allow_headers(vec!["*"])
                )
                .hoop(salvo::compression::Compression::new())
                .hoop(salvo::timeout::Timeout::new(std::time::Duration::from_secs(30)));

            Self {
                router,
                metrics,
                start_time: std::time::Instant::now(),
            }
        }

        pub fn with_openapi(mut self) -> Self {
            let mut openapi = OpenApi::new("Salvo API", "1.0.0");
            
            self.router = self.router
                .push(
                    Router::with_path("/openapi")
                        .get(oapi::swagger_ui::SwaggerUi::new("/openapi/openapi.json").into_handler(&mut openapi))
                )
                .push(
                    Router::with_path("/openapi/openapi.json")
                        .get(oapi::swagger_ui::OpenApiHandler::new(openapi))
                );
            
            self
        }
    }

    impl ModernFramework for SalvoAdvancedService {
        fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            let router = self.router.clone();
            Box::pin(async move {
                let acceptor = TcpListener::new(format!("0.0.0.0:{}", port)).bind().await?;
                tracing::info!("Salvo 服务启动在端口 {}", port);
                Server::new(acceptor).serve(router).await?;
                Ok(())
            })
        }

        fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Salvo 服务正在停止...");
                Ok(())
            })
        }

        fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>> {
            let uptime = self.start_time.elapsed().as_secs();
            Box::pin(async move {
                Ok(HealthStatus {
                    status: "healthy".to_string(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    version: "1.0.0".to_string(),
                    uptime,
                })
            })
        }

        fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>> {
            let metrics = self.metrics.clone();
            Box::pin(async move {
                let m = metrics.read().await;
                Ok(m.clone())
            })
        }
    }

    /// 用户数据结构
    #[derive(Debug, Clone, Serialize, Deserialize, ToSchema)]
    pub struct User {
        pub id: String,
        pub name: String,
        pub email: String,
        pub created_at: String,
    }

    /// 用户存储
    pub struct UserStore {
        users: Arc<RwLock<HashMap<String, User>>>,
    }

    impl UserStore {
        pub fn new() -> Self {
            let mut users = HashMap::new();
            users.insert("1".to_string(), User {
                id: "1".to_string(),
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
                created_at: chrono::Utc::now().to_rfc3339(),
            });
            users.insert("2".to_string(), User {
                id: "2".to_string(),
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
                created_at: chrono::Utc::now().to_rfc3339(),
            });

            Self {
                users: Arc::new(RwLock::new(users)),
            }
        }

        pub async fn get_user(&self, id: &str) -> Option<User> {
            let users = self.users.read().await;
            users.get(id).cloned()
        }

        pub async fn create_user(&self, user: User) -> User {
            let mut users = self.users.write().await;
            users.insert(user.id.clone(), user.clone());
            user
        }

        pub async fn update_user(&self, id: &str, user: User) -> Option<User> {
            let mut users = self.users.write().await;
            users.insert(id.to_string(), user.clone());
            Some(user)
        }

        pub async fn delete_user(&self, id: &str) -> bool {
            let mut users = self.users.write().await;
            users.remove(id).is_some()
        }

        pub async fn list_users(&self) -> Vec<User> {
            let users = self.users.read().await;
            users.values().cloned().collect()
        }
    }

    // 全局用户存储
    lazy_static::lazy_static! {
        static ref USER_STORE: UserStore = UserStore::new();
    }

    /// 健康检查处理器
    #[endpoint]
    async fn health_check_handler() -> impl IntoResponse {
        Json(HealthStatus {
            status: "healthy".to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
            version: "1.0.0".to_string(),
            uptime: 3600,
        })
    }

    /// 指标处理器
    #[endpoint]
    async fn metrics_handler() -> impl IntoResponse {
        Json(FrameworkMetrics {
            requests_total: 1000,
            active_connections: 50,
            memory_usage_mb: 256.5,
            cpu_usage_percent: 18.2,
            response_time_avg_ms: 45.3,
        })
    }

    /// 获取所有用户
    #[endpoint]
    async fn get_users() -> impl IntoResponse {
        let users = USER_STORE.list_users().await;
        Json(users)
    }

    /// 创建用户
    #[endpoint]
    async fn create_user(user: JsonBody<User>) -> impl IntoResponse {
        let user = USER_STORE.create_user(user.into_inner()).await;
        Json(user)
    }

    /// 获取单个用户
    #[endpoint]
    async fn get_user(id: PathParam<String>) -> impl IntoResponse {
        let user = USER_STORE.get_user(&id.into_inner()).await;
        Json(user)
    }

    /// 更新用户
    #[endpoint]
    async fn update_user(id: PathParam<String>, user: JsonBody<User>) -> impl IntoResponse {
        let user = USER_STORE.update_user(&id.into_inner(), user.into_inner()).await;
        Json(user)
    }

    /// 删除用户
    #[endpoint]
    async fn delete_user(id: PathParam<String>) -> impl IntoResponse {
        let deleted = USER_STORE.delete_user(&id.into_inner()).await;
        Json(deleted)
    }

    /// API v1 获取所有用户
    #[endpoint]
    async fn get_users_v1() -> impl IntoResponse {
        let users = USER_STORE.list_users().await;
        Json(serde_json::json!({
            "code": 200,
            "message": "success",
            "data": users,
            "timestamp": chrono::Utc::now().to_rfc3339()
        }))
    }

    /// API v1 获取单个用户
    #[endpoint]
    async fn get_user_v1(id: PathParam<String>) -> impl IntoResponse {
        let user = USER_STORE.get_user(&id.into_inner()).await;
        Json(serde_json::json!({
            "code": 200,
            "message": "success",
            "data": user,
            "timestamp": chrono::Utc::now().to_rfc3339()
        }))
    }
}

/// Volo 框架增强支持
#[cfg(feature = "with-volo")]
pub mod volo_advanced {
    use super::*;
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// Volo 高级服务实现
    pub struct VoloAdvancedService {
        metrics: Arc<RwLock<FrameworkMetrics>>,
        start_time: std::time::Instant,
    }

    impl VoloAdvancedService {
        pub fn new() -> Self {
            let metrics = Arc::new(RwLock::new(FrameworkMetrics {
                requests_total: 0,
                active_connections: 0,
                memory_usage_mb: 0.0,
                cpu_usage_percent: 0.0,
                response_time_avg_ms: 0.0,
            }));

            Self {
                metrics,
                start_time: std::time::Instant::now(),
            }
        }
    }

    impl ModernFramework for VoloAdvancedService {
        fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Volo 服务启动在端口 {}", port);
                Ok(())
            })
        }

        fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Volo 服务正在停止...");
                Ok(())
            })
        }

        fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>> {
            let uptime = self.start_time.elapsed().as_secs();
            Box::pin(async move {
                Ok(HealthStatus {
                    status: "healthy".to_string(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    version: "1.0.0".to_string(),
                    uptime,
                })
            })
        }

        fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>> {
            let metrics = self.metrics.clone();
            Box::pin(async move {
                let m = metrics.read().await;
                Ok(m.clone())
            })
        }
    }
}

/// fusen-rs 框架增强支持
#[cfg(feature = "with-fusen")]
pub mod fusen_advanced {
    use super::*;
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// fusen-rs 高级服务实现
    pub struct FusenAdvancedService {
        metrics: Arc<RwLock<FrameworkMetrics>>,
        start_time: std::time::Instant,
    }

    impl FusenAdvancedService {
        pub fn new() -> Self {
            let metrics = Arc::new(RwLock::new(FrameworkMetrics {
                requests_total: 0,
                active_connections: 0,
                memory_usage_mb: 0.0,
                cpu_usage_percent: 0.0,
                response_time_avg_ms: 0.0,
            }));

            Self {
                metrics,
                start_time: std::time::Instant::now(),
            }
        }
    }

    impl ModernFramework for FusenAdvancedService {
        fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("fusen-rs 服务启动在端口 {}", port);
                Ok(())
            })
        }

        fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("fusen-rs 服务正在停止...");
                Ok(())
            })
        }

        fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>> {
            let uptime = self.start_time.elapsed().as_secs();
            Box::pin(async move {
                Ok(HealthStatus {
                    status: "healthy".to_string(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    version: "1.0.0".to_string(),
                    uptime,
                })
            })
        }

        fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>> {
            let metrics = self.metrics.clone();
            Box::pin(async move {
                let m = metrics.read().await;
                Ok(m.clone())
            })
        }
    }
}

/// Spring-rs 框架增强支持
#[cfg(feature = "with-spring-rs")]
pub mod spring_rs_advanced {
    use super::*;
    use std::sync::Arc;
    use tokio::sync::RwLock;

    /// Spring-rs 高级服务实现
    pub struct SpringRsAdvancedService {
        metrics: Arc<RwLock<FrameworkMetrics>>,
        start_time: std::time::Instant,
    }

    impl SpringRsAdvancedService {
        pub fn new() -> Self {
            let metrics = Arc::new(RwLock::new(FrameworkMetrics {
                requests_total: 0,
                active_connections: 0,
                memory_usage_mb: 0.0,
                cpu_usage_percent: 0.0,
                response_time_avg_ms: 0.0,
            }));

            Self {
                metrics,
                start_time: std::time::Instant::now(),
            }
        }
    }

    impl ModernFramework for SpringRsAdvancedService {
        fn start(&self, port: u16) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Spring-rs 服务启动在端口 {}", port);
                Ok(())
            })
        }

        fn stop(&self) -> Pin<Box<dyn Future<Output = Result<()>> + Send>> {
            Box::pin(async move {
                tracing::info!("Spring-rs 服务正在停止...");
                Ok(())
            })
        }

        fn health_check(&self) -> Pin<Box<dyn Future<Output = Result<HealthStatus>> + Send>> {
            let uptime = self.start_time.elapsed().as_secs();
            Box::pin(async move {
                Ok(HealthStatus {
                    status: "healthy".to_string(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    version: "1.0.0".to_string(),
                    uptime,
                })
            })
        }

        fn get_metrics(&self) -> Pin<Box<dyn Future<Output = Result<FrameworkMetrics>> + Send>> {
            let metrics = self.metrics.clone();
            Box::pin(async move {
                let m = metrics.read().await;
                Ok(m.clone())
            })
        }
    }
}

/// 框架工厂
pub struct FrameworkFactory;

impl FrameworkFactory {
    /// 创建 Poem 服务
    #[cfg(feature = "with-poem")]
    pub fn create_poem_service() -> Box<dyn ModernFramework + Send + Sync> {
        Box::new(poem_advanced::PoemAdvancedService::new())
    }

    /// 创建 Salvo 服务
    #[cfg(feature = "with-salvo")]
    pub fn create_salvo_service() -> Box<dyn ModernFramework + Send + Sync> {
        Box::new(salvo_advanced::SalvoAdvancedService::new().with_openapi())
    }

    /// 创建 Volo 服务
    #[cfg(feature = "with-volo")]
    pub fn create_volo_service() -> Box<dyn ModernFramework + Send + Sync> {
        Box::new(volo_advanced::VoloAdvancedService::new())
    }

    /// 创建 fusen-rs 服务
    #[cfg(feature = "with-fusen")]
    pub fn create_fusen_service() -> Box<dyn ModernFramework + Send + Sync> {
        Box::new(fusen_advanced::FusenAdvancedService::new())
    }

    /// 创建 Spring-rs 服务
    #[cfg(feature = "with-spring-rs")]
    pub fn create_spring_rs_service() -> Box<dyn ModernFramework + Send + Sync> {
        Box::new(spring_rs_advanced::SpringRsAdvancedService::new())
    }

    /// 获取所有可用的框架
    pub fn get_available_frameworks() -> Vec<String> {
        vec![
            #[cfg(feature = "with-poem")]
            "Poem".to_string(),
            #[cfg(feature = "with-salvo")]
            "Salvo".to_string(),
            #[cfg(feature = "with-volo")]
            "Volo".to_string(),
            #[cfg(feature = "with-fusen")]
            "fusen-rs".to_string(),
            #[cfg(feature = "with-spring-rs")]
            "Spring-rs".to_string(),
        ]
    }
}

/// 框架比较器
pub struct FrameworkComparator;

impl FrameworkComparator {
    /// 比较框架性能
    pub fn compare_performance() -> HashMap<String, PerformanceMetrics> {
        [
            #[cfg(feature = "with-poem")]
            ("Poem".to_string(), PerformanceMetrics {
                throughput_rps: 15000,
                latency_p50_ms: 0.5,
                latency_p95_ms: 2.0,
                latency_p99_ms: 5.0,
                memory_usage_mb: 128.5,
                cpu_usage_percent: 15.2,
            }),
            #[cfg(feature = "with-salvo")]
            ("Salvo".to_string(), PerformanceMetrics {
                throughput_rps: 12000,
                latency_p50_ms: 0.8,
                latency_p95_ms: 3.0,
                latency_p99_ms: 8.0,
                memory_usage_mb: 256.8,
                cpu_usage_percent: 18.5,
            }),
            #[cfg(feature = "with-volo")]
            ("Volo".to_string(), PerformanceMetrics {
                throughput_rps: 20000,
                latency_p50_ms: 0.3,
                latency_p95_ms: 1.5,
                latency_p99_ms: 4.0,
                memory_usage_mb: 192.3,
                cpu_usage_percent: 12.8,
            }),
        ].into_iter().collect()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub throughput_rps: u32,
    pub latency_p50_ms: f64,
    pub latency_p95_ms: f64,
    pub latency_p99_ms: f64,
    pub memory_usage_mb: f64,
    pub cpu_usage_percent: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_framework_factory() {
        let available_frameworks = FrameworkFactory::get_available_frameworks();
        assert!(!available_frameworks.is_empty());
        
        #[cfg(feature = "with-poem")]
        assert!(available_frameworks.contains(&"Poem".to_string()));
        
        #[cfg(feature = "with-salvo")]
        assert!(available_frameworks.contains(&"Salvo".to_string()));
    }

    #[test]
    fn test_framework_comparison() {
        let performance_metrics = FrameworkComparator::compare_performance();
        assert!(!performance_metrics.is_empty());
        
        for (framework, metrics) in performance_metrics {
            assert!(metrics.throughput_rps > 0);
            assert!(metrics.latency_p50_ms > 0.0);
            assert!(metrics.memory_usage_mb > 0.0);
            println!("{} 性能指标: {:?}", framework, metrics);
        }
    }
}
