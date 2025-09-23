#![cfg(feature = "with-graphql")]
//! 高级 GraphQL 功能演示
//! 
//! 本示例展示了如何使用高级 GraphQL 功能：
//! - 查询、变更、订阅
//! - 数据加载器 (DataLoader)
//! - 批量查询优化
//! - 实时订阅
//! - 类型安全
//! - 性能监控

use std::collections::HashMap;
use anyhow::Result;
use tokio::time::{sleep, Duration};

// 导入我们的高级 GraphQL 模块
#[cfg(feature = "with-graphql")]
use c13_microservice::graphql_advanced::*;

/// GraphQL 演示管理器
pub struct GraphQLDemoManager {
    service: GraphQLService,
}

impl GraphQLDemoManager {
    pub fn new() -> Self {
        let config = GraphQLConfig {
            enable_introspection: true,
            enable_playground: true,
            max_query_depth: 15,
            max_query_complexity: 2000,
            query_timeout_ms: 30000,
            batch_size: 100,
            enable_tracing: true,
        };
        
        let service = GraphQLService::new(config);
        
        Self { service }
    }
    
    /// 演示基本查询
    #[cfg(feature = "with-graphql")]
    pub async fn demo_basic_queries(&self) -> Result<()> {
        println!("\n📝 演示基本查询:");
        println!("================================");
        
        // 获取所有用户
        let query = r#"
            query {
                users(limit: 5) {
                    id
                    name
                    email
                    age
                    createdAt
                }
            }
        "#;
        
        println!("查询: 获取前5个用户");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 根据ID获取用户
        let query = r#"
            query {
                user(id: "user_1") {
                    id
                    name
                    email
                    age
                }
            }
        "#;
        
        println!("\n查询: 根据ID获取用户");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 搜索用户
        let query = r#"
            query {
                searchUsers(input: { query: "User 1", limit: 3 }) {
                    id
                    name
                    email
                }
            }
        "#;
        
        println!("\n查询: 搜索用户");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        Ok(())
    }
    
    /// 演示高级查询
    #[cfg(feature = "with-graphql")]
    pub async fn demo_advanced_queries(&self) -> Result<()> {
        println!("\n🔍 演示高级查询:");
        println!("================================");
        
        // 分页查询
        let query = r#"
            query {
                usersConnection(first: 3, after: "0") {
                    edges {
                        node {
                            id
                            name
                            email
                        }
                        cursor
                    }
                    pageInfo {
                        hasNextPage
                        hasPreviousPage
                        startCursor
                        endCursor
                    }
                    totalCount
                }
            }
        "#;
        
        println!("查询: 分页获取用户");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 获取产品
        let query = r#"
            query {
                products(category: "Electronics", limit: 3) {
                    id
                    name
                    description
                    price
                    category
                    stock
                }
            }
        "#;
        
        println!("\n查询: 获取电子产品");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 获取用户订单
        let query = r#"
            query {
                userOrders(userId: "user_1") {
                    id
                    userId
                    total
                    status
                    products {
                        productId
                        quantity
                        price
                    }
                }
            }
        "#;
        
        println!("\n查询: 获取用户订单");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 健康检查
        let query = r#"
            query {
                health
                serviceInfo {
                    name
                    version
                    description
                    uptime
                }
            }
        "#;
        
        println!("\n查询: 服务信息");
        let response = self.service.execute_query(query).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        Ok(())
    }
    
    /// 演示变更操作
    #[cfg(feature = "with-graphql")]
    pub async fn demo_mutations(&self) -> Result<()> {
        println!("\n✏️  演示变更操作:");
        println!("================================");
        
        // 创建用户
        let mutation = r#"
            mutation {
                createUser(input: {
                    name: "新用户"
                    email: "newuser@example.com"
                    age: 25
                }) {
                    id
                    name
                    email
                    age
                    createdAt
                }
            }
        "#;
        
        println!("变更: 创建用户");
        let response = self.service.execute_query(mutation).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 更新用户
        let mutation = r#"
            mutation {
                updateUser(id: "user_1", input: {
                    name: "更新的用户"
                    age: 30
                }) {
                    id
                    name
                    email
                    age
                    updatedAt
                }
            }
        "#;
        
        println!("\n变更: 更新用户");
        let response = self.service.execute_query(mutation).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 批量创建用户
        let mutation = r#"
            mutation {
                createUsers(inputs: [
                    {
                        name: "批量用户1"
                        email: "batch1@example.com"
                        age: 20
                    },
                    {
                        name: "批量用户2"
                        email: "batch2@example.com"
                        age: 22
                    }
                ]) {
                    id
                    name
                    email
                    age
                }
            }
        "#;
        
        println!("\n变更: 批量创建用户");
        let response = self.service.execute_query(mutation).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        // 删除用户
        let mutation = r#"
            mutation {
                deleteUser(id: "user_2")
            }
        "#;
        
        println!("\n变更: 删除用户");
        let response = self.service.execute_query(mutation).await?;
        println!("响应: {}", serde_json::to_string_pretty(&response)?);
        
        Ok(())
    }
    
    /// 演示订阅功能
    #[cfg(feature = "with-graphql")]
    pub async fn demo_subscriptions(&self) -> Result<()> {
        println!("\n📡 演示订阅功能:");
        println!("================================");
        
        // 用户创建事件订阅
        let subscription = r#"
            subscription {
                userCreated {
                    id
                    name
                    email
                    age
                }
            }
        "#;
        
        println!("订阅: 用户创建事件");
        println!("注意: 实际订阅需要 WebSocket 连接");
        println!("这里仅演示订阅查询结构");
        println!("查询: {}", subscription);
        
        // 服务状态订阅
        let subscription = r#"
            subscription {
                serviceStatus
            }
        "#;
        
        println!("\n订阅: 服务状态更新");
        println!("查询: {}", subscription);
        
        // 实时指标订阅
        let subscription = r#"
            subscription {
                realTimeMetrics {
                    timestamp
                    cpuUsage
                    memoryUsage
                    activeConnections
                }
            }
        "#;
        
        println!("\n订阅: 实时指标");
        println!("查询: {}", subscription);
        
        Ok(())
    }
    
    /// 演示数据加载器
    #[cfg(feature = "with-graphql")]
    pub async fn demo_data_loader(&self) -> Result<()> {
        println!("\n🔄 演示数据加载器:");
        println!("================================");
        
        let data_loader = self.service.get_data_loader();
        
        // 单个用户加载
        println!("单个用户加载:");
        let user = data_loader.load_user("user_1").await;
        match user {
            Some(user) => println!("  用户: {:?}", user.name),
            None => println!("  用户未找到"),
        }
        
        // 批量用户加载
        println!("\n批量用户加载:");
        let user_ids = vec!["user_1".to_string(), "user_2".to_string(), "user_3".to_string()];
        let users = data_loader.load_users(user_ids).await;
        
        for (id, user) in users {
            match user {
                Some(user) => println!("  {}: {}", id, user.name),
                None => println!("  {}: 未找到", id),
            }
        }
        
        // 批量产品加载
        println!("\n批量产品加载:");
        let product_ids = vec!["product_1".to_string(), "product_2".to_string(), "product_3".to_string()];
        let products = data_loader.load_products(product_ids).await;
        
        for (id, product) in products {
            match product {
                Some(product) => println!("  {}: {} (${:.2})", id, product.name, product.price),
                None => println!("  {}: 未找到", id),
            }
        }
        
        Ok(())
    }
    
    /// 演示批量查询优化
    #[cfg(feature = "with-graphql")]
    pub async fn demo_batch_queries(&self) -> Result<()> {
        println!("\n📦 演示批量查询优化:");
        println!("================================");
        
        let queries = vec![
            r#"{ users(limit: 3) { id name email } }"#,
            r#"{ products(category: "Electronics", limit: 3) { id name price } }"#,
            r#"{ health }"#,
            r#"{ serviceInfo { name version } }"#,
        ];
        
        println!("执行 {} 个并发查询...", queries.len());
        
        let start_time = std::time::Instant::now();
        let handles: Vec<_> = queries.into_iter()
            .map(|query| {
                let service = &self.service;
                tokio::spawn(async move {
                    service.execute_query(query).await
                })
            })
            .collect();
        
        let mut success_count = 0;
        let mut total_time = 0;
        
        for (i, handle) in handles.into_iter().enumerate() {
            match handle.await {
                Ok(Ok(response)) => {
                    success_count += 1;
                    println!("  查询 {}: 成功", i + 1);
                }
                Ok(Err(e)) => {
                    println!("  查询 {}: 失败 - {}", i + 1, e);
                }
                Err(e) => {
                    println!("  查询 {}: 任务失败 - {}", i + 1, e);
                }
            }
        }
        
        let total_time_elapsed = start_time.elapsed().as_millis() as u64;
        
        println!("\n批量查询结果:");
        println!("  - 成功查询: {}/{}", success_count, 4);
        println!("  - 总耗时: {}ms", total_time_elapsed);
        println!("  - 平均查询时间: {}ms", total_time_elapsed / 4);
        
        Ok(())
    }
    
    /// 演示性能基准测试
    #[cfg(feature = "with-graphql")]
    pub async fn demo_performance_benchmark(&self) -> Result<()> {
        println!("\n⚡ 演示性能基准测试:");
        println!("================================");
        
        let iterations = 100;
        let mut total_time = 0;
        let mut success_count = 0;
        
        println!("执行 {} 次用户查询...", iterations);
        
        for i in 1..=iterations {
            let query = r#"
                query {
                    users(limit: 5) {
                        id
                        name
                        email
                    }
                }
            "#;
            
            let start = std::time::Instant::now();
            match self.service.execute_query(query).await {
                Ok(_) => {
                    let duration = start.elapsed().as_millis() as u64;
                    total_time += duration;
                    success_count += 1;
                    
                    if i % 20 == 0 {
                        println!("  已完成 {}/{} 查询", i, iterations);
                    }
                }
                Err(e) => {
                    println!("  查询 {} 失败: {}", i, e);
                }
            }
        }
        
        let average_time = if success_count > 0 { total_time / success_count } else { 0 };
        let throughput = if total_time > 0 { (success_count as f64 * 1000.0) / total_time as f64 } else { 0.0 };
        
        println!("\n基准测试结果:");
        println!("  - 总查询数: {}", iterations);
        println!("  - 成功查询数: {}", success_count);
        println!("  - 成功率: {:.2}%", (success_count as f64 / iterations as f64) * 100.0);
        println!("  - 平均响应时间: {}ms", average_time);
        println!("  - 吞吐量: {:.2} queries/s", throughput);
        
        Ok(())
    }
    
    /// 演示 Schema 信息
    #[cfg(feature = "with-graphql")]
    pub async fn demo_schema_info(&self) -> Result<()> {
        println!("\n📋 演示 Schema 信息:");
        println!("================================");
        
        let schema_sdl = self.service.get_schema_sdl();
        println!("GraphQL Schema SDL:");
        println!("{}", schema_sdl);
        
        Ok(())
    }
    
    /// 演示配置管理
    pub async fn demo_configuration_management(&self) -> Result<()> {
        println!("\n⚙️  演示配置管理:");
        println!("================================");
        
        let config = self.service.get_config();
        println!("当前配置:");
        println!("  - 启用内省: {}", config.enable_introspection);
        println!("  - 启用 Playground: {}", config.enable_playground);
        println!("  - 最大查询深度: {}", config.max_query_depth);
        println!("  - 最大查询复杂度: {}", config.max_query_complexity);
        println!("  - 查询超时: {}ms", config.query_timeout_ms);
        println!("  - 批处理大小: {}", config.batch_size);
        println!("  - 启用追踪: {}", config.enable_tracing);
        
        println!("\n配置建议:");
        if config.max_query_depth > 10 {
            println!("  - 查询深度较高，建议监控性能");
        }
        if config.batch_size > 100 {
            println!("  - 批处理大小较大，建议监控内存使用");
        }
        if config.query_timeout_ms < 30000 {
            println!("  - 查询超时较短，可能影响复杂查询");
        }
        
        Ok(())
    }
    
    /// 演示类型安全
    #[cfg(feature = "with-graphql")]
    pub async fn demo_type_safety(&self) -> Result<()> {
        println!("\n🛡️  演示类型安全:");
        println!("================================");
        
        // 演示类型安全的查询
        let valid_query = r#"
            query {
                users(limit: 5) {
                    id
                    name
                    email
                    age
                }
            }
        "#;
        
        println!("有效查询:");
        let response = self.service.execute_query(valid_query).await?;
        if response.errors.is_empty() {
            println!("  ✅ 查询执行成功，类型安全");
        } else {
            println!("  ❌ 查询执行失败: {:?}", response.errors);
        }
        
        // 演示类型错误的查询
        let invalid_query = r#"
            query {
                users(limit: "invalid") {
                    id
                    name
                    invalidField
                }
            }
        "#;
        
        println!("\n无效查询 (类型错误):");
        let response = self.service.execute_query(invalid_query).await?;
        if !response.errors.is_empty() {
            println!("  ✅ 类型检查正确捕获错误: {:?}", response.errors);
        } else {
            println!("  ❌ 类型检查未捕获错误");
        }
        
        Ok(())
    }
}

/// 主函数演示高级 GraphQL 功能
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 高级 GraphQL 功能演示");
    println!("================================");
    
    // 检查是否启用了 GraphQL 功能
    #[cfg(not(feature = "with-graphql"))]
    {
        println!("⚠️  GraphQL 功能未启用");
        println!("请使用以下命令启用:");
        println!("  cargo run --example advanced_graphql_demo --features with-graphql");
        return Ok(());
    }
    
    // 创建 GraphQL 演示管理器
    let demo_manager = GraphQLDemoManager::new();
    
    // 演示基本查询
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_basic_queries().await?;
    
    // 演示高级查询
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_advanced_queries().await?;
    
    // 演示变更操作
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_mutations().await?;
    
    // 演示订阅功能
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_subscriptions().await?;
    
    // 演示数据加载器
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_data_loader().await?;
    
    // 演示批量查询优化
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_batch_queries().await?;
    
    // 演示性能基准测试
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_performance_benchmark().await?;
    
    // 演示类型安全
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_type_safety().await?;
    
    // 演示 Schema 信息
    #[cfg(feature = "with-graphql")]
    demo_manager.demo_schema_info().await?;
    
    // 演示配置管理
    demo_manager.demo_configuration_management().await?;
    
    println!("\n✅ 高级 GraphQL 功能演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 完整的查询、变更、订阅支持");
    println!("- 数据加载器 (DataLoader) 批量优化");
    println!("- 分页和连接模式");
    println!("- 实时订阅和事件流");
    println!("- 类型安全和验证");
    println!("- 性能监控和基准测试");
    println!("- 灵活的配置管理");
    println!("- Schema 内省和文档生成");
    println!();
    println!("📚 GraphQL 最佳实践:");
    println!("- 使用 DataLoader 避免 N+1 查询问题");
    println!("- 合理设置查询深度和复杂度限制");
    println!("- 启用查询缓存提高性能");
    println!("- 使用订阅实现实时功能");
    println!("- 类型安全确保数据一致性");
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_graphql_demo_manager() {
        let demo_manager = GraphQLDemoManager::new();
        let config = demo_manager.service.get_config();
        assert!(config.enable_introspection);
    }

    #[cfg(feature = "with-graphql")]
    #[tokio::test]
    async fn test_basic_query() {
        let demo_manager = GraphQLDemoManager::new();
        let query = r#"{ health }"#;
        let response = demo_manager.service.execute_query(query).await.unwrap();
        assert!(response.errors.is_empty());
    }

    #[tokio::test]
    async fn test_data_store() {
        let data_store = DataStore::new();
        let users = data_store.get_users(Some(5), None).await;
        assert_eq!(users.len(), 5);
    }
}
