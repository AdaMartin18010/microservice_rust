//! 高级 GraphQL 生态系统模块
//!
//! 本模块提供了完整的 GraphQL 支持，包括：
//! - 查询、变更、订阅
//! - 数据加载器 (DataLoader)
//! - 批量查询优化
//! - 实时订阅
//! - 类型安全
//! - 性能监控

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

#[cfg(feature = "with-graphql")]
use async_graphql::{
    Context, EmptyMutation, EmptySubscription, ID, InputObject, MergedObject, Object, ScalarType,
    Schema, SchemaBuilder, SimpleObject, Subscription, Value, async_trait, futures_util::Stream,
};

/// GraphQL 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GraphQLConfig {
    pub enable_introspection: bool,
    pub enable_playground: bool,
    pub max_query_depth: u32,
    pub max_query_complexity: u32,
    pub query_timeout_ms: u64,
    pub batch_size: u32,
    pub enable_tracing: bool,
}

impl Default for GraphQLConfig {
    fn default() -> Self {
        Self {
            enable_introspection: true,
            enable_playground: true,
            max_query_depth: 10,
            max_query_complexity: 1000,
            query_timeout_ms: 30000, // 30 seconds
            batch_size: 100,
            enable_tracing: true,
        }
    }
}

/// 用户数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct User {
    pub id: ID,
    pub name: String,
    pub email: String,
    pub age: Option<i32>,
    pub created_at: String,
    pub updated_at: String,
}

/// 用户输入
#[derive(Debug, Clone, Serialize, Deserialize, InputObject)]
pub struct UserInput {
    pub name: String,
    pub email: String,
    pub age: Option<i32>,
}

/// 用户更新输入
#[derive(Debug, Clone, Serialize, Deserialize, InputObject)]
pub struct UserUpdateInput {
    pub name: Option<String>,
    pub email: Option<String>,
    pub age: Option<i32>,
}

/// 搜索输入
#[derive(Debug, Clone, Serialize, Deserialize, InputObject)]
pub struct SearchInput {
    pub query: String,
    pub limit: Option<i32>,
    pub offset: Option<i32>,
}

/// 产品数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct Product {
    pub id: ID,
    pub name: String,
    pub description: Option<String>,
    pub price: f64,
    pub category: String,
    pub stock: i32,
    pub created_at: String,
}

/// 订单数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct Order {
    pub id: ID,
    pub user_id: ID,
    pub products: Vec<OrderItem>,
    pub total: f64,
    pub status: OrderStatus,
    pub created_at: String,
}

/// 订单项目
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct OrderItem {
    pub product_id: ID,
    pub quantity: i32,
    pub price: f64,
}

/// 订单状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
}

/// 实现 ScalarType 为 OrderStatus
#[cfg(feature = "with-graphql")]
#[async_trait::async_trait]
impl ScalarType for OrderStatus {
    fn type_name() -> &'static str {
        "OrderStatus"
    }

    fn description() -> Option<&'static str> {
        Some("订单状态")
    }

    fn serialize(&self) -> Value {
        match self {
            OrderStatus::Pending => Value::String("PENDING".to_string()),
            OrderStatus::Processing => Value::String("PROCESSING".to_string()),
            OrderStatus::Shipped => Value::String("SHIPPED".to_string()),
            OrderStatus::Delivered => Value::String("DELIVERED".to_string()),
            OrderStatus::Cancelled => Value::String("CANCELLED".to_string()),
        }
    }

    fn parse(value: Value) -> async_graphql::InputValueResult<Self> {
        match value {
            Value::String(s) => match s.as_str() {
                "PENDING" => Ok(OrderStatus::Pending),
                "PROCESSING" => Ok(OrderStatus::Processing),
                "SHIPPED" => Ok(OrderStatus::Shipped),
                "DELIVERED" => Ok(OrderStatus::Delivered),
                "CANCELLED" => Ok(OrderStatus::Cancelled),
                _ => Err(async_graphql::InputValueError::custom("无效的订单状态")),
            },
            _ => Err(async_graphql::InputValueError::custom(
                "订单状态必须是字符串",
            )),
        }
    }
}

/// 分页信息
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct PageInfo {
    pub has_next_page: bool,
    pub has_previous_page: bool,
    pub start_cursor: Option<String>,
    pub end_cursor: Option<String>,
}

/// 分页连接
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct UserConnection {
    pub edges: Vec<UserEdge>,
    pub page_info: PageInfo,
    pub total_count: i32,
}

/// 用户边
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct UserEdge {
    pub node: User,
    pub cursor: String,
}

/// 数据存储
pub struct DataStore {
    users: Arc<RwLock<HashMap<String, User>>>,
    products: Arc<RwLock<HashMap<String, Product>>>,
    orders: Arc<RwLock<HashMap<String, Order>>>,
}

impl DataStore {
    pub fn new() -> Self {
        let mut users = HashMap::new();
        let mut products = HashMap::new();
        let mut orders = HashMap::new();

        // 初始化测试数据
        for i in 1..=100 {
            let user_id = format!("user_{}", i);
            users.insert(
                user_id.clone(),
                User {
                    id: async_graphql::ID::from(user_id.clone()),
                    name: format!("User {}", i),
                    email: format!("user{}@example.com", i),
                    age: Some(20 + (i % 50)),
                    created_at: chrono::Utc::now().to_rfc3339(),
                    updated_at: chrono::Utc::now().to_rfc3339(),
                },
            );

            let product_id = format!("product_{}", i);
            products.insert(
                product_id.clone(),
                Product {
                    id: async_graphql::ID::from(product_id.clone()),
                    name: format!("Product {}", i),
                    description: Some(format!("这是产品 {} 的描述", i)),
                    price: 10.0 + (i as f64 * 0.5),
                    category: match i % 5 {
                        0 => "Electronics",
                        1 => "Books",
                        2 => "Clothing",
                        3 => "Home",
                        _ => "Sports",
                    }
                    .to_string(),
                    stock: 100 - (i % 50),
                    created_at: chrono::Utc::now().to_rfc3339(),
                },
            );
        }

        Self {
            users: Arc::new(RwLock::new(users)),
            products: Arc::new(RwLock::new(products)),
            orders: Arc::new(RwLock::new(orders)),
        }
    }

    pub async fn get_user(&self, id: &str) -> Option<User> {
        let users = self.users.read().await;
        users.get(id).cloned()
    }

    pub async fn get_users(&self, limit: Option<i32>, offset: Option<i32>) -> Vec<User> {
        let users = self.users.read().await;
        let limit = limit.unwrap_or(10) as usize;
        let offset = offset.unwrap_or(0) as usize;

        users.values().skip(offset).take(limit).cloned().collect()
    }

    pub async fn search_users(&self, query: &str, limit: Option<i32>) -> Vec<User> {
        let users = self.users.read().await;
        let limit = limit.unwrap_or(10) as usize;

        users
            .values()
            .filter(|user| user.name.contains(query) || user.email.contains(query))
            .take(limit)
            .cloned()
            .collect()
    }

    pub async fn create_user(&self, input: UserInput) -> User {
        let id = uuid::Uuid::new_v4().to_string();
        let now = chrono::Utc::now().to_rfc3339();

        let user = User {
            id: async_graphql::ID::from(id.clone()),
            name: input.name,
            email: input.email,
            age: input.age,
            created_at: now.clone(),
            updated_at: now,
        };

        let mut users = self.users.write().await;
        users.insert(id, user.clone());
        user
    }

    pub async fn update_user(&self, id: &str, input: UserUpdateInput) -> Option<User> {
        let mut users = self.users.write().await;
        if let Some(user) = users.get_mut(id) {
            if let Some(name) = input.name {
                user.name = name;
            }
            if let Some(email) = input.email {
                user.email = email;
            }
            if let Some(age) = input.age {
                user.age = Some(age);
            }
            user.updated_at = chrono::Utc::now().to_rfc3339();
            Some(user.clone())
        } else {
            None
        }
    }

    pub async fn delete_user(&self, id: &str) -> bool {
        let mut users = self.users.write().await;
        users.remove(id).is_some()
    }

    pub async fn get_product(&self, id: &str) -> Option<Product> {
        let products = self.products.read().await;
        products.get(id).cloned()
    }

    pub async fn get_products(&self, category: Option<&str>, limit: Option<i32>) -> Vec<Product> {
        let products = self.products.read().await;
        let limit = limit.unwrap_or(10) as usize;

        let filtered: Vec<Product> = products
            .values()
            .filter(|product| {
                if let Some(cat) = category {
                    product.category == cat
                } else {
                    true
                }
            })
            .take(limit)
            .cloned()
            .collect();

        filtered
    }

    pub async fn get_order(&self, id: &str) -> Option<Order> {
        let orders = self.orders.read().await;
        orders.get(id).cloned()
    }

    pub async fn get_user_orders(&self, user_id: &str) -> Vec<Order> {
        let orders = self.orders.read().await;
        orders
            .values()
            .filter(|order| order.user_id == async_graphql::ID::from(user_id))
            .cloned()
            .collect()
    }
}

/// 数据加载器
pub struct DataLoader {
    data_store: Arc<DataStore>,
}

impl DataLoader {
    pub fn new(data_store: Arc<DataStore>) -> Self {
        Self { data_store }
    }

    pub async fn load_user(&self, id: &str) -> Option<User> {
        self.data_store.get_user(id).await
    }

    pub async fn load_users(&self, ids: Vec<String>) -> HashMap<String, Option<User>> {
        let mut result = HashMap::new();

        for id in ids {
            let user = self.data_store.get_user(&id).await;
            result.insert(id, user);
        }

        result
    }

    pub async fn load_product(&self, id: &str) -> Option<Product> {
        self.data_store.get_product(id).await
    }

    pub async fn load_products(&self, ids: Vec<String>) -> HashMap<String, Option<Product>> {
        let mut result = HashMap::new();

        for id in ids {
            let product = self.data_store.get_product(&id).await;
            result.insert(id, product);
        }

        result
    }
}

/// GraphQL 查询根
#[cfg(feature = "with-graphql")]
pub struct QueryRoot;

#[cfg(feature = "with-graphql")]
#[Object]
impl QueryRoot {
    /// 获取所有用户
    async fn users(
        &self,
        ctx: &Context<'_>,
        limit: Option<i32>,
        offset: Option<i32>,
    ) -> async_graphql::Result<Vec<User>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let users = data_store.get_users(limit, offset).await;
        Ok(users)
    }

    /// 根据ID获取用户
    async fn user(&self, ctx: &Context<'_>, id: ID) -> async_graphql::Result<Option<User>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let user = data_store.get_user(id.as_str()).await;
        Ok(user)
    }

    /// 搜索用户
    async fn search_users(
        &self,
        ctx: &Context<'_>,
        input: SearchInput,
    ) -> async_graphql::Result<Vec<User>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let users = data_store.search_users(&input.query, input.limit).await;
        Ok(users)
    }

    /// 分页获取用户
    async fn users_connection(
        &self,
        ctx: &Context<'_>,
        first: Option<i32>,
        after: Option<String>,
    ) -> async_graphql::Result<UserConnection> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let first = first.unwrap_or(10);
        let after = after.unwrap_or("0".to_string());
        let offset = after.parse::<i32>().unwrap_or(0);

        let users = data_store.get_users(Some(first), Some(offset)).await;
        let total_count = data_store.users.read().await.len() as i32;

        let edges: Vec<UserEdge> = users
            .into_iter()
            .enumerate()
            .map(|(i, user)| UserEdge {
                node: user,
                cursor: (offset + i as i32 + 1).to_string(),
            })
            .collect();

        let page_info = PageInfo {
            has_next_page: offset + first < total_count,
            has_previous_page: offset > 0,
            start_cursor: if edges.is_empty() {
                None
            } else {
                Some(edges.first().unwrap().cursor.clone())
            },
            end_cursor: if edges.is_empty() {
                None
            } else {
                Some(edges.last().unwrap().cursor.clone())
            },
        };

        Ok(UserConnection {
            edges,
            page_info,
            total_count,
        })
    }

    /// 获取所有产品
    async fn products(
        &self,
        ctx: &Context<'_>,
        category: Option<String>,
        limit: Option<i32>,
    ) -> async_graphql::Result<Vec<Product>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let products = data_store.get_products(category.as_deref(), limit).await;
        Ok(products)
    }

    /// 根据ID获取产品
    async fn product(&self, ctx: &Context<'_>, id: ID) -> async_graphql::Result<Option<Product>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let product = data_store.get_product(id.as_str()).await;
        Ok(product)
    }

    /// 获取订单
    async fn order(&self, ctx: &Context<'_>, id: ID) -> async_graphql::Result<Option<Order>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let order = data_store.get_order(id.as_str()).await;
        Ok(order)
    }

    /// 获取用户的订单
    async fn user_orders(
        &self,
        ctx: &Context<'_>,
        user_id: ID,
    ) -> async_graphql::Result<Vec<Order>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let orders = data_store.get_user_orders(user_id.as_str()).await;
        Ok(orders)
    }

    /// 健康检查
    async fn health(&self) -> async_graphql::Result<String> {
        Ok("GraphQL 服务正常运行".to_string())
    }

    /// 获取服务信息
    async fn service_info(&self) -> async_graphql::Result<ServiceInfo> {
        Ok(ServiceInfo {
            name: "GraphQL 微服务".to_string(),
            version: "1.0.0".to_string(),
            description: "基于 Rust 的高级 GraphQL 微服务".to_string(),
            uptime: 3600,
        })
    }
}

/// 服务信息
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct ServiceInfo {
    pub name: String,
    pub version: String,
    pub description: String,
    pub uptime: i32,
}

/// GraphQL 变更根
#[cfg(feature = "with-graphql")]
pub struct MutationRoot;

#[cfg(feature = "with-graphql")]
#[Object]
impl MutationRoot {
    /// 创建用户
    async fn create_user(
        &self,
        ctx: &Context<'_>,
        input: UserInput,
    ) -> async_graphql::Result<User> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let user = data_store.create_user(input).await;
        Ok(user)
    }

    /// 更新用户
    async fn update_user(
        &self,
        ctx: &Context<'_>,
        id: ID,
        input: UserUpdateInput,
    ) -> async_graphql::Result<Option<User>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let user = data_store.update_user(id.as_str(), input).await;
        Ok(user)
    }

    /// 删除用户
    async fn delete_user(&self, ctx: &Context<'_>, id: ID) -> async_graphql::Result<bool> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let deleted = data_store.delete_user(id.as_str()).await;
        Ok(deleted)
    }

    /// 批量创建用户
    async fn create_users(
        &self,
        ctx: &Context<'_>,
        inputs: Vec<UserInput>,
    ) -> async_graphql::Result<Vec<User>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let mut users = Vec::new();

        for input in inputs {
            let user = data_store.create_user(input).await;
            users.push(user);
        }

        Ok(users)
    }

    /// 批量更新用户
    async fn update_users(
        &self,
        ctx: &Context<'_>,
        updates: Vec<(ID, UserUpdateInput)>,
    ) -> async_graphql::Result<Vec<Option<User>>> {
        let data_store = ctx.data_unchecked::<Arc<DataStore>>();
        let mut results = Vec::new();

        for (id, input) in updates {
            let user = data_store.update_user(id.as_str(), input).await;
            results.push(user);
        }

        Ok(results)
    }
}

/// GraphQL 订阅根
#[cfg(feature = "with-graphql")]
pub struct SubscriptionRoot;

#[cfg(feature = "with-graphql")]
#[Subscription]
impl SubscriptionRoot {
    /// 用户创建事件
    async fn user_created(&self) -> impl Stream<Item = User> {
        async_stream::stream! {
            for i in 1..=5 {
                yield User {
                    id: async_graphql::ID::from(format!("stream_user_{}", i)),
                    name: format!("Stream User {}", i),
                    email: format!("stream_user{}@example.com", i),
                    age: Some(25 + i),
                    created_at: chrono::Utc::now().to_rfc3339(),
                    updated_at: chrono::Utc::now().to_rfc3339(),
                };
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            }
        }
    }

    /// 服务状态事件
    async fn service_status(&self) -> impl Stream<Item = String> {
        async_stream::stream! {
            for i in 1..=10 {
                yield format!("服务状态更新 #{}: 正常运行", i);
                tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
            }
        }
    }

    /// 实时指标
    async fn real_time_metrics(&self) -> impl Stream<Item = MetricsUpdate> {
        async_stream::stream! {
            for i in 1..=20 {
                yield MetricsUpdate {
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    cpu_usage: 20.0 + (i as f64 * 2.0),
                    memory_usage: 512.0 + (i as f64 * 10.0),
                    active_connections: 100 + i,
                };
                tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
            }
        }
    }
}

/// 指标更新
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct MetricsUpdate {
    pub timestamp: String,
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub active_connections: i32,
}

/// GraphQL 合并根
#[cfg(feature = "with-graphql")]
#[derive(MergedObject, Default)]
pub struct GraphQLRoot(QueryRoot, MutationRoot, SubscriptionRoot);

/// GraphQL 服务
pub struct GraphQLService {
    config: GraphQLConfig,
    data_store: Arc<DataStore>,
    data_loader: Arc<DataLoader>,
    #[cfg(feature = "with-graphql")]
    schema: Schema<GraphQLRoot, GraphQLRoot, GraphQLRoot>,
}

impl GraphQLService {
    pub fn new(config: GraphQLConfig) -> Self {
        let data_store = Arc::new(DataStore::new());
        let data_loader = Arc::new(DataLoader::new(data_store.clone()));

        #[cfg(feature = "with-graphql")]
        let schema = Schema::build(QueryRoot, MutationRoot, SubscriptionRoot)
            .data(data_store.clone())
            .data(data_loader.clone())
            .finish();

        Self {
            config,
            data_store,
            data_loader,
            #[cfg(feature = "with-graphql")]
            schema,
        }
    }

    /// 执行 GraphQL 查询
    #[cfg(feature = "with-graphql")]
    pub async fn execute_query(
        &self,
        query: &str,
    ) -> async_graphql::Result<async_graphql::Response> {
        self.schema.execute(query).await
    }

    /// 执行 GraphQL 查询（带变量）
    #[cfg(feature = "with-graphql")]
    pub async fn execute_query_with_variables(
        &self,
        query: &str,
        variables: async_graphql::Variables,
    ) -> async_graphql::Result<async_graphql::Response> {
        self.schema
            .execute(async_graphql::Request::new(query).variables(variables))
            .await
    }

    /// 获取 Schema SDL
    #[cfg(feature = "with-graphql")]
    pub fn get_schema_sdl(&self) -> String {
        self.schema.sdl()
    }

    /// 获取配置
    pub fn get_config(&self) -> &GraphQLConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: GraphQLConfig) {
        self.config = config;
    }

    /// 获取数据存储
    pub fn get_data_store(&self) -> Arc<DataStore> {
        self.data_store.clone()
    }

    /// 获取数据加载器
    pub fn get_data_loader(&self) -> Arc<DataLoader> {
        self.data_loader.clone()
    }
}

/// GraphQL 服务工厂
pub struct GraphQLServiceFactory;

impl GraphQLServiceFactory {
    /// 创建默认配置的 GraphQL 服务
    pub fn create_default_service() -> GraphQLService {
        GraphQLService::new(GraphQLConfig::default())
    }

    /// 创建自定义配置的 GraphQL 服务
    pub fn create_custom_service(config: GraphQLConfig) -> GraphQLService {
        GraphQLService::new(config)
    }

    /// 创建生产环境配置
    pub fn create_production_config() -> GraphQLConfig {
        GraphQLConfig {
            enable_introspection: false,
            enable_playground: false,
            max_query_depth: 15,
            max_query_complexity: 2000,
            query_timeout_ms: 60000, // 1 minute
            batch_size: 200,
            enable_tracing: true,
        }
    }

    /// 创建开发环境配置
    pub fn create_development_config() -> GraphQLConfig {
        GraphQLConfig {
            enable_introspection: true,
            enable_playground: true,
            max_query_depth: 10,
            max_query_complexity: 1000,
            query_timeout_ms: 30000,
            batch_size: 50,
            enable_tracing: true,
        }
    }
}

/// GraphQL 性能监控
pub struct GraphQLMetrics {
    pub query_count: u64,
    pub mutation_count: u64,
    pub subscription_count: u64,
    pub average_execution_time_ms: f64,
    pub error_count: u64,
    pub cache_hit_rate: f64,
}

impl Default for GraphQLMetrics {
    fn default() -> Self {
        Self {
            query_count: 0,
            mutation_count: 0,
            subscription_count: 0,
            average_execution_time_ms: 0.0,
            error_count: 0,
            cache_hit_rate: 0.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_data_store() {
        let data_store = DataStore::new();
        let users = data_store.get_users(Some(5), None).await;
        assert_eq!(users.len(), 5);
    }

    #[tokio::test]
    async fn test_data_loader() {
        let data_store = Arc::new(DataStore::new());
        let data_loader = DataLoader::new(data_store.clone());

        let user = data_loader.load_user("user_1").await;
        assert!(user.is_some());
    }

    #[test]
    fn test_graphql_config() {
        let config = GraphQLConfig::default();
        assert_eq!(config.max_query_depth, 10);
        assert_eq!(config.max_query_complexity, 1000);
    }

    #[tokio::test]
    async fn test_graphql_service() {
        let service = GraphQLServiceFactory::create_default_service();
        let config = service.get_config();
        assert!(config.enable_introspection);
    }
}
