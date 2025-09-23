//! Spring-rs 微服务框架支持
//! 
//! Spring-rs 是受 Java 的 Spring Boot 启发的 Rust 微服务框架

#[cfg(feature = "with-spring-rs")]
pub mod application;
#[cfg(feature = "with-spring-rs")]
pub mod configuration;
#[cfg(feature = "with-spring-rs")]
pub mod beans;

#[cfg(feature = "with-spring-rs")]
pub use application::*;
#[cfg(feature = "with-spring-rs")]
pub use configuration::*;
#[cfg(feature = "with-spring-rs")]
pub use beans::*;

/// Spring-rs 框架的常用类型和函数
#[cfg(feature = "with-spring-rs")]
pub mod prelude {
    pub use serde::{Deserialize, Serialize};
    pub use tracing::{info, warn, error};
}

/// Spring-rs 应用配置
#[cfg(feature = "with-spring-rs")]
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SpringRsConfig {
    pub application_name: String,
    pub server_port: u16,
    pub profiles: Vec<String>,
    pub database_url: Option<String>,
    pub redis_url: Option<String>,
}

impl Default for SpringRsConfig {
    fn default() -> Self {
        Self {
            application_name: "spring-rs-app".to_string(),
            server_port: 8080,
            profiles: vec!["default".to_string()],
            database_url: None,
            redis_url: None,
        }
    }
}

/// Spring-rs 应用
#[cfg(feature = "with-spring-rs")]
pub struct SpringRsApplication {
    config: SpringRsConfig,
}

#[cfg(feature = "with-spring-rs")]
impl SpringRsApplication {
    pub fn new(config: SpringRsConfig) -> Self {
        Self { config }
    }
    
    pub async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        tracing::info!("启动 Spring-rs 应用: {:?}", self.config);
        // 这里需要实现具体的 Spring-rs 应用启动逻辑
        Ok(())
    }
}

/// 创建基础的 Spring-rs 应用
#[cfg(feature = "with-spring-rs")]
pub fn create_application(config: SpringRsConfig) -> SpringRsApplication {
    SpringRsApplication::new(config)
}
