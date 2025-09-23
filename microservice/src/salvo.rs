//! Salvo 微服务框架支持
//! 
//! Salvo 是一个功能强大的 Rust Web 框架，提供了丰富的中间件和路由功能

#[cfg(feature = "with-salvo")]
pub mod handlers;
#[cfg(feature = "with-salvo")]
pub mod middleware;
#[cfg(feature = "with-salvo")]
pub mod routes;

#[cfg(feature = "with-salvo")]
pub use handlers::*;
#[cfg(feature = "with-salvo")]
pub use middleware::*;
#[cfg(feature = "with-salvo")]
pub use routes::*;

/// Salvo 框架的常用类型和函数
#[cfg(feature = "with-salvo")]
pub mod prelude {
    pub use salvo::{
        prelude::*,
        oapi::{
            self, extract::*,
            openapi::OpenApi,
            ToSchema, ToResponse,
        },
    };
    pub use serde::{Deserialize, Serialize};
    pub use tracing::{info, warn, error};
}

/// 创建基础的 Salvo 应用
#[cfg(feature = "with-salvo")]
pub fn create_app() -> salvo::Router {
    use salvo::prelude::*;
    
    Router::new()
        .push(
            Router::with_path("/health")
                .get(health_check)
        )
        .push(
            Router::with_path("/metrics")
                .get(metrics)
        )
        .hoop(salvo::logging::Logger::new())
        .hoop(salvo::cors::Cors::new().allow_origin("*").allow_methods(vec!["GET", "POST", "PUT", "DELETE"]))
}

/// 健康检查处理器
#[cfg(feature = "with-salvo")]
#[endpoint]
async fn health_check() -> impl salvo::IntoResponse {
    salvo::web::Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339()
    }))
}

/// 指标处理器
#[cfg(feature = "with-salvo")]
#[endpoint]
async fn metrics() -> impl salvo::IntoResponse {
    salvo::web::Json(serde_json::json!({
        "requests_total": 1000,
        "active_connections": 50,
        "memory_usage": "256MB"
    }))
}
