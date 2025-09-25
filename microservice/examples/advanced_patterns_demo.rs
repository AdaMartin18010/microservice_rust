//! 高级微服务模式演示
//!
//! 本示例展示了高级微服务架构模式：
//! - CQRS (命令查询职责分离)
//! - Event Sourcing (事件溯源)
//! - Saga 模式 (分布式事务)

use anyhow::Result;
use chrono::Utc;
use std::collections::HashMap;

// 导入我们的高级模式模块
use microservice::advanced_patterns::*;

/// 高级模式演示管理器
pub struct AdvancedPatternsDemoManager {
    service: AdvancedPatternsService,
}

impl AdvancedPatternsDemoManager {
    pub fn new() -> Self {
        let service = AdvancedPatternsServiceFactory::create_service();
        Self { service }
    }

    /// 演示 CQRS 模式
    pub async fn demo_cqrs_pattern(&self) -> Result<()> {
        println!("\n🔄 演示 CQRS 模式:");
        println!("================================");

        // 创建用户命令
        let create_command = CreateUserCommand {
            id: "user_001".to_string(),
            name: "Alice Johnson".to_string(),
            email: "alice.johnson@example.com".to_string(),
            age: Some(28),
            timestamp: Utc::now(),
        };

        println!("执行创建用户命令:");
        let events = self.service.execute_command(create_command).await?;
        println!("✅ 命令执行成功，生成了 {} 个事件", events.len());

        // 查询用户
        let query = GetUserQuery {
            id: "user_001".to_string(),
            parameters: HashMap::new(),
        };

        match self
            .service
            .execute_query::<GetUserQuery, Option<UserReadModel>>(query)
            .await
        {
            Ok(Some(user)) => {
                println!("✅ 查询成功: {} ({})", user.name, user.email);
            }
            Ok(None) => println!("❌ 用户未找到"),
            Err(e) => println!("❌ 查询失败: {}", e),
        }

        Ok(())
    }

    /// 演示 Saga 模式
    pub async fn demo_saga_pattern(&self) -> Result<()> {
        println!("\n🎭 演示 Saga 模式:");
        println!("================================");

        // 成功的订单 Saga
        let order_id = "order_001";
        let user_id = "user_001";
        let product_id = "product_001";
        let quantity = 2;

        match self
            .service
            .execute_saga(
                order_id.to_string(),
                user_id.to_string(),
                product_id.to_string(),
                quantity,
            )
            .await
        {
            Ok(_) => println!("✅ 订单 Saga 执行成功"),
            Err(e) => println!("❌ 订单 Saga 执行失败: {}", e),
        }

        Ok(())
    }
}

/// 主函数演示高级微服务模式
#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    println!("🚀 高级微服务模式演示");
    println!("================================");

    let demo_manager = AdvancedPatternsDemoManager::new();

    // 演示 CQRS 模式
    demo_manager.demo_cqrs_pattern().await?;

    // 演示 Saga 模式
    demo_manager.demo_saga_pattern().await?;

    println!("\n✅ 高级微服务模式演示完成！");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cqrs_pattern() {
        let demo_manager = AdvancedPatternsDemoManager::new();
        let result = demo_manager.demo_cqrs_pattern().await;
        assert!(result.is_ok());
    }
}
