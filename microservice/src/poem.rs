//! Poem 微服务框架支持
//!
//! Poem 是一个现代化的 Rust Web 框架，具有高性能、易用性和丰富的功能

#[cfg(feature = "with-poem")]
pub mod handlers;
#[cfg(feature = "with-poem")]
pub mod middleware;
#[cfg(feature = "with-poem")]
pub mod routes;

#[cfg(feature = "with-poem")]
pub use handlers::*;
#[cfg(feature = "with-poem")]
pub use middleware::*;
#[cfg(feature = "with-poem")]
pub use routes::*;

/// Poem 框架的常用类型和函数
#[cfg(feature = "with-poem")]
pub mod prelude {
    pub use poem::{
        EndpointExt, Route, Server, delete, get, handler,
        listener::TcpListener,
        middleware::Tracing,
        post, put,
        web::{Json, Path, Query},
    };
    pub use serde::{Deserialize, Serialize};
    pub use tracing::{error, info, warn};
}

/// 创建基础的 Poem 应用
#[cfg(feature = "with-poem")]
pub fn create_app() -> poem::Route {
    use poem::prelude::*;

    Route::new()
        .at("/health", get(health_check))
        .at("/metrics", get(metrics))
        .with(poem::middleware::Tracing)
}

/// 健康检查处理器
#[cfg(feature = "with-poem")]
#[handler]
async fn health_check() -> poem::web::Json<serde_json::Value> {
    poem::web::Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339()
    }))
}

/// 指标处理器
#[cfg(feature = "with-poem")]
#[handler]
async fn metrics() -> poem::web::Json<serde_json::Value> {
    poem::web::Json(serde_json::json!({
        "requests_total": 1000,
        "active_connections": 50,
        "memory_usage": "256MB"
    }))
}
