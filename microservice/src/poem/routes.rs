//! Poem 框架路由模块
//! 
//! 提供各种常用的路由配置和组合

use poem::{
    get, handler, listener::TcpListener, middleware::Tracing, post, put, delete,
    EndpointExt, Route, Server, web::{Json, Path, Query},
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{info, warn, error};

use super::handlers::*;
use super::middleware::*;

/// 基础路由配置
pub fn create_base_routes() -> Route {
    Route::new()
        .at("/health", get(health_check))
        .at("/health/detailed", get(health_check_detailed))
        .at("/metrics", get(metrics))
        .at("/version", get(version))
        .at("/config", get(config))
        .at("/status", get(status))
}

/// 管理路由配置
pub fn create_admin_routes() -> Route {
    Route::new()
        .at("/admin/health", get(health_check_detailed))
        .at("/admin/metrics", get(metrics))
        .at("/admin/version", get(version))
        .at("/admin/config", get(config))
        .at("/admin/status", get(status))
        .at("/admin/memory", get(memory_usage))
        .at("/admin/cpu", get(cpu_usage))
        .at("/admin/network", get(network_stats))
}

/// 测试路由配置
pub fn create_test_routes() -> Route {
    Route::new()
        .at("/test/error", get(error_example))
        .at("/test/delay", get(delay_example))
        .at("/test/retry", get(retry_example))
        .at("/test/load", get(load_test))
}

/// API路由配置
pub fn create_api_routes() -> Route {
    Route::new()
        .nest("/api/v1", create_v1_routes())
        .nest("/api/v2", create_v2_routes())
}

/// V1 API路由
pub fn create_v1_routes() -> Route {
    Route::new()
        .at("/health", get(health_check))
        .at("/metrics", get(metrics))
        .at("/users", get(get_users_v1).post(create_user_v1))
        .at("/users/:id", get(get_user_v1).put(update_user_v1).delete(delete_user_v1))
}

/// V2 API路由
pub fn create_v2_routes() -> Route {
    Route::new()
        .at("/health", get(health_check_detailed))
        .at("/metrics", get(metrics))
        .at("/users", get(get_users_v2).post(create_user_v2))
        .at("/users/:id", get(get_user_v2).put(update_user_v2).delete(delete_user_v2))
        .at("/users/search", get(search_users_v2))
}

/// 用户数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub created_at: String,
}

/// 创建用户请求
#[derive(Debug, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

/// 更新用户请求
#[derive(Debug, Serialize, Deserialize)]
pub struct UpdateUserRequest {
    pub name: Option<String>,
    pub email: Option<String>,
}

/// 用户搜索参数
#[derive(Debug, Serialize, Deserialize)]
pub struct UserSearchQuery {
    pub name: Option<String>,
    pub email: Option<String>,
    pub page: Option<u32>,
    pub limit: Option<u32>,
}

// V1 API 处理器
#[handler]
async fn get_users_v1() -> PoemResult<Json<ApiResponse<Vec<User>>>> {
    info!("V1 API: 获取用户列表");
    
    let users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            created_at: "2024-01-01T00:00:00Z".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            created_at: "2024-01-02T00:00:00Z".to_string(),
        },
    ];
    
    Ok(Json(ApiResponse::success(users)))
}

#[handler]
async fn get_user_v1(Path(id): Path<u64>) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V1 API: 获取用户 {}", id);
    
    if id == 1 {
        let user = User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            created_at: "2024-01-01T00:00:00Z".to_string(),
        };
        Ok(Json(ApiResponse::success(user)))
    } else {
        Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id))))
    }
}

#[handler]
async fn create_user_v1(Json(request): Json<CreateUserRequest>) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V1 API: 创建用户 {:?}", request);
    
    let user = User {
        id: 3,
        name: request.name,
        email: request.email,
        created_at: chrono::Utc::now().to_rfc3339(),
    };
    
    Ok(Json(ApiResponse::success(user)))
}

#[handler]
async fn update_user_v1(
    Path(id): Path<u64>,
    Json(request): Json<UpdateUserRequest>,
) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V1 API: 更新用户 {} {:?}", id, request);
    
    if id == 1 {
        let user = User {
            id: 1,
            name: request.name.unwrap_or_else(|| "Alice".to_string()),
            email: request.email.unwrap_or_else(|| "alice@example.com".to_string()),
            created_at: "2024-01-01T00:00:00Z".to_string(),
        };
        Ok(Json(ApiResponse::success(user)))
    } else {
        Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id))))
    }
}

#[handler]
async fn delete_user_v1(Path(id): Path<u64>) -> PoemResult<Json<ApiResponse<String>>> {
    info!("V1 API: 删除用户 {}", id);
    
    if id == 1 {
        Ok(Json(ApiResponse::success(format!("用户 {} 已删除", id))))
    } else {
        Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id))))
    }
}

// V2 API 处理器
#[handler]
async fn get_users_v2() -> PoemResult<Json<ApiResponse<Vec<User>>>> {
    info!("V2 API: 获取用户列表");
    
    let users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            created_at: "2024-01-01T00:00:00Z".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            created_at: "2024-01-02T00:00:00Z".to_string(),
        },
        User {
            id: 3,
            name: "Charlie".to_string(),
            email: "charlie@example.com".to_string(),
            created_at: "2024-01-03T00:00:00Z".to_string(),
        },
    ];
    
    Ok(Json(ApiResponse::success(users)))
}

#[handler]
async fn get_user_v2(Path(id): Path<u64>) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V2 API: 获取用户 {}", id);
    
    match id {
        1 => {
            let user = User {
                id: 1,
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
                created_at: "2024-01-01T00:00:00Z".to_string(),
            };
            Ok(Json(ApiResponse::success(user)))
        }
        2 => {
            let user = User {
                id: 2,
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
                created_at: "2024-01-02T00:00:00Z".to_string(),
            };
            Ok(Json(ApiResponse::success(user)))
        }
        _ => Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id)))),
    }
}

#[handler]
async fn create_user_v2(Json(request): Json<CreateUserRequest>) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V2 API: 创建用户 {:?}", request);
    
    let user = User {
        id: 4,
        name: request.name,
        email: request.email,
        created_at: chrono::Utc::now().to_rfc3339(),
    };
    
    Ok(Json(ApiResponse::success(user)))
}

#[handler]
async fn update_user_v2(
    Path(id): Path<u64>,
    Json(request): Json<UpdateUserRequest>,
) -> PoemResult<Json<ApiResponse<User>>> {
    info!("V2 API: 更新用户 {} {:?}", id, request);
    
    match id {
        1 => {
            let user = User {
                id: 1,
                name: request.name.unwrap_or_else(|| "Alice".to_string()),
                email: request.email.unwrap_or_else(|| "alice@example.com".to_string()),
                created_at: "2024-01-01T00:00:00Z".to_string(),
            };
            Ok(Json(ApiResponse::success(user)))
        }
        2 => {
            let user = User {
                id: 2,
                name: request.name.unwrap_or_else(|| "Bob".to_string()),
                email: request.email.unwrap_or_else(|| "bob@example.com".to_string()),
                created_at: "2024-01-02T00:00:00Z".to_string(),
            };
            Ok(Json(ApiResponse::success(user)))
        }
        _ => Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id)))),
    }
}

#[handler]
async fn delete_user_v2(Path(id): Path<u64>) -> PoemResult<Json<ApiResponse<String>>> {
    info!("V2 API: 删除用户 {}", id);
    
    match id {
        1 | 2 => Ok(Json(ApiResponse::success(format!("用户 {} 已删除", id)))),
        _ => Ok(Json(ApiResponse::error(format!("用户 {} 未找到", id)))),
    }
}

#[handler]
async fn search_users_v2(Query(query): Query<UserSearchQuery>) -> PoemResult<Json<ApiResponse<Vec<User>>>> {
    info!("V2 API: 搜索用户 {:?}", query);
    
    let mut users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            created_at: "2024-01-01T00:00:00Z".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            created_at: "2024-01-02T00:00:00Z".to_string(),
        },
        User {
            id: 3,
            name: "Charlie".to_string(),
            email: "charlie@example.com".to_string(),
            created_at: "2024-01-03T00:00:00Z".to_string(),
        },
    ];
    
    // 简单的搜索过滤
    if let Some(name) = &query.name {
        users.retain(|user| user.name.contains(name));
    }
    
    if let Some(email) = &query.email {
        users.retain(|user| user.email.contains(email));
    }
    
    // 分页处理
    let page = query.page.unwrap_or(1);
    let limit = query.limit.unwrap_or(10);
    let start = ((page - 1) * limit) as usize;
    let end = (start + limit as usize).min(users.len());
    
    if start < users.len() {
        users = users[start..end].to_vec();
    } else {
        users = Vec::new();
    }
    
    Ok(Json(ApiResponse::success(users)))
}

/// 创建完整的应用路由
pub fn create_app_routes() -> Route {
    Route::new()
        .nest("/", create_base_routes())
        .nest("/admin", create_admin_routes())
        .nest("/test", create_test_routes())
        .nest("/", create_api_routes())
        .with(Tracing)
        .with(create_middleware_stack())
}

/// 创建微服务路由
pub fn create_microservice_routes() -> Route {
    Route::new()
        .at("/health", get(health_check))
        .at("/metrics", get(metrics))
        .at("/version", get(version))
        .at("/status", get(status))
        .with(Tracing)
        .with(PerformanceMiddleware)
        .with(RequestIdMiddleware)
        .with(SecurityHeadersMiddleware)
}
