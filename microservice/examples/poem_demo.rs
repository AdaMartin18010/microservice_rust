//! Poem 微服务框架演示（简化版本）
//!
//! 本示例展示了如何使用 Poem 框架的概念构建微服务
//! 注意：这是一个简化版本，不依赖外部 poem 库

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;

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

/// API响应结构
#[derive(Debug, Serialize, Deserialize)]
pub struct ApiResponse<T> {
    pub success: bool,
    pub data: Option<T>,
    pub message: Option<String>,
    pub error: Option<String>,
}

impl<T> ApiResponse<T> {
    pub fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            message: None,
            error: None,
        }
    }

    pub fn error(message: String) -> Self {
        Self {
            success: false,
            data: None,
            message: None,
            error: Some(message),
        }
    }
}

/// 简化的 Poem 风格服务
#[derive(Debug)]
pub struct PoemStyleService {
    users: Arc<RwLock<HashMap<u64, User>>>,
    next_id: Arc<RwLock<u64>>,
}

impl PoemStyleService {
    pub fn new() -> Self {
        Self {
            users: Arc::new(RwLock::new(HashMap::new())),
            next_id: Arc::new(RwLock::new(1)),
        }
    }

    /// 创建用户
    pub async fn create_user(&self, request: CreateUserRequest) -> Result<ApiResponse<User>> {
        info!("创建用户: {}", request.name);
        let mut next_id = self.next_id.write().await;
        let id = *next_id;
        *next_id += 1;
        let user = User {
            id,
            name: request.name.clone(),
            email: request.email.clone(),
            created_at: chrono::Utc::now().to_rfc3339(),
        };
        self.users.write().await.insert(id, user.clone());
        Ok(ApiResponse::success(user))
    }

    /// 获取用户
    pub async fn get_user(&self, id: u64) -> Result<ApiResponse<User>> {
        info!("获取用户: {}", id);
        let users = self.users.read().await;
        match users.get(&id) {
            Some(user) => Ok(ApiResponse::success(user.clone())),
            None => Ok(ApiResponse::error(format!("用户 {} 不存在", id))),
        }
    }

    /// 获取所有用户
    pub async fn get_users(&self) -> Result<ApiResponse<Vec<User>>> {
        info!("获取所有用户");
        let users = self.users.read().await;
        let user_list: Vec<User> = users.values().cloned().collect();
        Ok(ApiResponse::success(user_list))
    }

    /// 更新用户
    pub async fn update_user(
        &self,
        id: u64,
        request: UpdateUserRequest,
    ) -> Result<ApiResponse<User>> {
        info!("更新用户: {}", id);
        let mut users = self.users.write().await;
        match users.get_mut(&id) {
            Some(user) => {
                if let Some(name) = request.name {
                    user.name = name;
                }
                if let Some(email) = request.email {
                    user.email = email;
                }
                Ok(ApiResponse::success(user.clone()))
            }
            None => Ok(ApiResponse::error(format!("用户 {} 不存在", id))),
        }
    }

    /// 删除用户
    pub async fn delete_user(&self, id: u64) -> Result<ApiResponse<String>> {
        info!("删除用户: {}", id);
        let mut users = self.users.write().await;
        match users.remove(&id) {
            Some(_) => Ok(ApiResponse::success(format!("用户 {} 已删除", id))),
            None => Ok(ApiResponse::error(format!("用户 {} 不存在", id))),
        }
    }

    /// 获取用户统计
    pub async fn get_stats(&self) -> Result<ApiResponse<HashMap<String, u64>>> {
        info!("获取用户统计");
        let users = self.users.read().await;
        let mut stats = HashMap::new();
        stats.insert("total_users".to_string(), users.len() as u64);
        Ok(ApiResponse::success(stats))
    }
}

impl Default for PoemStyleService {
    fn default() -> Self {
        Self::new()
    }
}

/// 简化的 HTTP 请求处理器
#[derive(Debug)]
pub struct HttpHandler {
    service: PoemStyleService,
}

impl HttpHandler {
    pub fn new() -> Self {
        Self {
            service: PoemStyleService::new(),
        }
    }

    /// 模拟 HTTP GET 请求
    pub async fn handle_get(&self, path: &str) -> Result<String> {
        match path {
            "/users" => {
                let response = self.service.get_users().await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            path if path.starts_with("/users/") => {
                let id_str = &path[7..];
                if let Ok(id) = id_str.parse::<u64>() {
                    let response = self.service.get_user(id).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的用户ID".to_string()),
                    )?)
                }
            }
            "/stats" => {
                let response = self.service.get_stats().await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            _ => Ok(serde_json::to_string_pretty(
                &ApiResponse::<String>::error("未找到路径".to_string()),
            )?),
        }
    }

    /// 模拟 HTTP POST 请求
    pub async fn handle_post(&self, path: &str, body: &str) -> Result<String> {
        match path {
            "/users" => {
                let request: CreateUserRequest = serde_json::from_str(body)?;
                let response = self.service.create_user(request).await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            _ => Ok(serde_json::to_string_pretty(
                &ApiResponse::<String>::error("未找到路径".to_string()),
            )?),
        }
    }

    /// 模拟 HTTP PUT 请求
    pub async fn handle_put(&self, path: &str, body: &str) -> Result<String> {
        match path {
            path if path.starts_with("/users/") => {
                let id_str = &path[7..];
                if let Ok(id) = id_str.parse::<u64>() {
                    let request: UpdateUserRequest = serde_json::from_str(body)?;
                    let response = self.service.update_user(id, request).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的用户ID".to_string()),
                    )?)
                }
            }
            _ => Ok(serde_json::to_string_pretty(
                &ApiResponse::<String>::error("未找到路径".to_string()),
            )?),
        }
    }

    /// 模拟 HTTP DELETE 请求
    pub async fn handle_delete(&self, path: &str) -> Result<String> {
        match path {
            path if path.starts_with("/users/") => {
                let id_str = &path[7..];
                if let Ok(id) = id_str.parse::<u64>() {
                    let response = self.service.delete_user(id).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的用户ID".to_string()),
                    )?)
                }
            }
            _ => Ok(serde_json::to_string_pretty(
                &ApiResponse::<String>::error("未找到路径".to_string()),
            )?),
        }
    }
}

impl Default for HttpHandler {
    fn default() -> Self {
        Self::new()
    }
}

/// 主函数演示 Poem 风格的服务
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Poem 风格微服务演示");
    println!("================================");

    let handler = HttpHandler::new();

    // 演示创建用户
    println!("\n📝 创建用户:");
    let create_request = CreateUserRequest {
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
    };
    let response = handler
        .handle_post("/users", &serde_json::to_string(&create_request)?)
        .await?;
    println!("POST /users: {}", response);

    // 创建更多用户
    let users_to_create = vec![
        ("李四", "lisi@example.com"),
        ("王五", "wangwu@example.com"),
        ("赵六", "zhaoliu@example.com"),
    ];

    for (name, email) in users_to_create {
        let request = CreateUserRequest {
            name: name.to_string(),
            email: email.to_string(),
        };
        handler
            .handle_post("/users", &serde_json::to_string(&request)?)
            .await?;
    }

    // 演示获取所有用户
    println!("\n👥 获取所有用户:");
    let response = handler.handle_get("/users").await?;
    println!("GET /users: {}", response);

    // 演示获取特定用户
    println!("\n👤 获取特定用户:");
    let response = handler.handle_get("/users/1").await?;
    println!("GET /users/1: {}", response);

    // 演示更新用户
    println!("\n✏️  更新用户:");
    let update_request = UpdateUserRequest {
        name: Some("张三（更新）".to_string()),
        email: None,
    };
    let response = handler
        .handle_put("/users/1", &serde_json::to_string(&update_request)?)
        .await?;
    println!("PUT /users/1: {}", response);

    // 演示获取统计信息
    println!("\n📊 获取统计信息:");
    let response = handler.handle_get("/stats").await?;
    println!("GET /stats: {}", response);

    // 演示删除用户
    println!("\n🗑️  删除用户:");
    let response = handler.handle_delete("/users/2").await?;
    println!("DELETE /users/2: {}", response);

    // 演示获取更新后的用户列表
    println!("\n👥 获取更新后的用户列表:");
    let response = handler.handle_get("/users").await?;
    println!("GET /users: {}", response);

    println!("\n✅ Poem 风格微服务演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- RESTful API 设计");
    println!("- JSON 序列化/反序列化");
    println!("- 异步处理");
    println!("- 错误处理");
    println!("- 用户管理功能");
    println!("- 统计信息");
    println!();
    println!("📚 框架特点:");
    println!("- 高性能异步处理");
    println!("- 类型安全的请求/响应");
    println!("- 中间件支持");
    println!("- 易于扩展");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_create_user() {
        let service = PoemStyleService::new();
        let request = CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };

        let response = service.create_user(request).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "测试用户");
    }

    #[tokio::test]
    async fn test_get_user() {
        let service = PoemStyleService::new();

        // 创建用户
        let request = CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        service.create_user(request).await.unwrap();

        // 获取用户
        let response = service.get_user(1).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "测试用户");
    }

    #[tokio::test]
    async fn test_update_user() {
        let service = PoemStyleService::new();

        // 创建用户
        let request = CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        service.create_user(request).await.unwrap();

        // 更新用户
        let update_request = UpdateUserRequest {
            name: Some("更新后的用户".to_string()),
            email: None,
        };
        let response = service.update_user(1, update_request).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "更新后的用户");
    }

    #[tokio::test]
    async fn test_delete_user() {
        let service = PoemStyleService::new();

        // 创建用户
        let request = CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        service.create_user(request).await.unwrap();

        // 删除用户
        let response = service.delete_user(1).await.unwrap();
        assert!(response.success);

        // 验证用户已删除
        let response = service.get_user(1).await.unwrap();
        assert!(!response.success);
    }
}
