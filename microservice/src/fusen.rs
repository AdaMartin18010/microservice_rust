//! fusen-rs 微服务框架支持
//! 
//! fusen-rs 是基于 Rust 开发的高性能微服务框架，支持多种协议和跨语言调用

#[cfg(feature = "with-fusen")]
pub mod services;
#[cfg(feature = "with-fusen")]
pub mod client;
#[cfg(feature = "with-fusen")]
pub mod registry;

#[cfg(feature = "with-fusen")]
pub use services::*;
#[cfg(feature = "with-fusen")]
pub use client::*;
#[cfg(feature = "with-fusen")]
pub use registry::*;

/// fusen-rs 框架的常用类型和函数
#[cfg(feature = "with-fusen")]
pub mod prelude {
    pub use serde::{Deserialize, Serialize};
    pub use tracing::{info, warn, error};
}

/// 基础 fusen-rs 服务配置
#[cfg(feature = "with-fusen")]
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct FusenConfig {
    pub service_name: String,
    pub version: String,
    pub port: u16,
    pub registry_url: String,
    pub protocol: String,
}

impl Default for FusenConfig {
    fn default() -> Self {
        Self {
            service_name: "default-service".to_string(),
            version: "1.0.0".to_string(),
            port: 8080,
            registry_url: "http://localhost:8848".to_string(),
            protocol: "dubbo".to_string(),
        }
    }
}

/// 创建基础的 fusen-rs 服务
#[cfg(feature = "with-fusen")]
pub fn create_service(config: FusenConfig) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("创建 fusen-rs 服务: {:?}", config);
    // 这里需要实现具体的 fusen-rs 服务创建逻辑
    Ok(())
}
