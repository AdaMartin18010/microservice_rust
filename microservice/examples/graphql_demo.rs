#![cfg(feature = "with-graphql")]
//! GraphQL 微服务演示
//! 
//! 本示例展示了如何使用 GraphQL 构建现代微服务API
//! 包括：Schema定义、Resolver实现、订阅支持、数据加载器等

use async_graphql::{
    Context, EmptyMutation, EmptySubscription, Object, Schema, SimpleObject, ID,
    Result as GraphQLResult, InputObject, Enum, Subscription, async_stream,
};
use async_graphql_poem::{GraphQLRequest, GraphQLResponse};
use poem::{
    handler, listener::TcpListener, middleware::Tracing, post, EndpointExt, Route, Server,
    web::Json,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn, error};
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 用户数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct User {
    pub id: ID,
    pub name: String,
    pub email: String,
    pub age: Option<i32>,
    pub created_at: DateTime<Utc>,
    pub posts: Vec<Post>,
    pub profile: Option<UserProfile>,
}

/// 用户档案
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct UserProfile {
    pub bio: Option<String>,
    pub avatar_url: Option<String>,
    pub location: Option<String>,
    pub website: Option<String>,
}

/// 文章数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct Post {
    pub id: ID,
    pub title: String,
    pub content: String,
    pub author_id: ID,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub tags: Vec<String>,
    pub comments: Vec<Comment>,
}

/// 评论数据结构
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct Comment {
    pub id: ID,
    pub content: String,
    pub author_id: ID,
    pub post_id: ID,
    pub created_at: DateTime<Utc>,
}

/// 用户输入类型
#[derive(Debug, InputObject)]
pub struct CreateUserInput {
    pub name: String,
    pub email: String,
    pub age: Option<i32>,
}

/// 文章输入类型
#[derive(Debug, InputObject)]
pub struct CreatePostInput {
    pub title: String,
    pub content: String,
    pub author_id: ID,
    pub tags: Vec<String>,
}

/// 评论输入类型
#[derive(Debug, InputObject)]
pub struct CreateCommentInput {
    pub content: String,
    pub author_id: ID,
    pub post_id: ID,
}

/// 排序枚举
#[derive(Debug, Enum, Copy, Clone, Eq, PartialEq)]
pub enum SortOrder {
    Asc,
    Desc,
}

/// 分页输入
#[derive(Debug, InputObject)]
pub struct PaginationInput {
    pub page: Option<i32>,
    pub limit: Option<i32>,
    pub sort_by: Option<String>,
    pub sort_order: Option<SortOrder>,
}

/// 搜索输入
#[derive(Debug, InputObject)]
pub struct SearchInput {
    pub query: String,
    pub filters: Option<HashMap<String, String>>,
}

/// 数据存储
pub struct DataStore {
    users: Arc<RwLock<HashMap<String, User>>>,
    posts: Arc<RwLock<HashMap<String, Post>>>,
    comments: Arc<RwLock<HashMap<String, Comment>>>,
}

impl DataStore {
    pub fn new() -> Self {
        let mut users = HashMap::new();
        let mut posts = HashMap::new();
        let mut comments = HashMap::new();
        
        // 创建示例数据
        let user1_id = "user-1".to_string();
        let user2_id = "user-2".to_string();
        
        let user1 = User {
            id: ID::from(&user1_id),
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            age: Some(25),
            created_at: Utc::now(),
            posts: vec![],
            profile: Some(UserProfile {
                bio: Some("Software Engineer".to_string()),
                avatar_url: Some("https://example.com/avatar1.jpg".to_string()),
                location: Some("San Francisco".to_string()),
                website: Some("https://alice.dev".to_string()),
            }),
        };
        
        let user2 = User {
            id: ID::from(&user2_id),
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            age: Some(30),
            created_at: Utc::now(),
            posts: vec![],
            profile: Some(UserProfile {
                bio: Some("Product Manager".to_string()),
                avatar_url: Some("https://example.com/avatar2.jpg".to_string()),
                location: Some("New York".to_string()),
                website: Some("https://bob.dev".to_string()),
            }),
        };
        
        users.insert(user1_id.clone(), user1);
        users.insert(user2_id.clone(), user2);
        
        let post1_id = "post-1".to_string();
        let post1 = Post {
            id: ID::from(&post1_id),
            title: "Getting Started with GraphQL".to_string(),
            content: "GraphQL is a powerful query language for APIs...".to_string(),
            author_id: ID::from(&user1_id),
            created_at: Utc::now(),
            updated_at: Utc::now(),
            tags: vec!["graphql".to_string(), "api".to_string()],
            comments: vec![],
        };
        
        let post2_id = "post-2".to_string();
        let post2 = Post {
            id: ID::from(&post2_id),
            title: "Rust for Microservices".to_string(),
            content: "Rust is an excellent choice for building microservices...".to_string(),
            author_id: ID::from(&user2_id),
            created_at: Utc::now(),
            updated_at: Utc::now(),
            tags: vec!["rust".to_string(), "microservices".to_string()],
            comments: vec![],
        };
        
        posts.insert(post1_id.clone(), post1);
        posts.insert(post2_id.clone(), post2);
        
        let comment1_id = "comment-1".to_string();
        let comment1 = Comment {
            id: ID::from(&comment1_id),
            content: "Great article!".to_string(),
            author_id: ID::from(&user2_id),
            post_id: ID::from(&post1_id),
            created_at: Utc::now(),
        };
        
        comments.insert(comment1_id, comment1);
        
        Self {
            users: Arc::new(RwLock::new(users)),
            posts: Arc::new(RwLock::new(posts)),
            comments: Arc::new(RwLock::new(comments)),
        }
    }
}

/// GraphQL 查询根
pub struct QueryRoot;

#[Object]
impl QueryRoot {
    /// 获取所有用户
    async fn users(&self, ctx: &Context<'_>) -> GraphQLResult<Vec<User>> {
        info!("GraphQL: 查询所有用户");
        let store = ctx.data::<DataStore>()?;
        let users = store.users.read().await;
        Ok(users.values().cloned().collect())
    }
    
    /// 根据ID获取用户
    async fn user(&self, ctx: &Context<'_>, id: ID) -> GraphQLResult<Option<User>> {
        info!("GraphQL: 查询用户 {}", id);
        let store = ctx.data::<DataStore>()?;
        let users = store.users.read().await;
        Ok(users.get(&id.to_string()).cloned())
    }
    
    /// 搜索用户
    async fn search_users(
        &self,
        ctx: &Context<'_>,
        input: SearchInput,
    ) -> GraphQLResult<Vec<User>> {
        info!("GraphQL: 搜索用户 - {}", input.query);
        let store = ctx.data::<DataStore>()?;
        let users = store.users.read().await;
        
        let results: Vec<User> = users
            .values()
            .filter(|user| {
                user.name.contains(&input.query) || user.email.contains(&input.query)
            })
            .cloned()
            .collect();
        
        Ok(results)
    }
    
    /// 获取所有文章
    async fn posts(&self, ctx: &Context<'_>) -> GraphQLResult<Vec<Post>> {
        info!("GraphQL: 查询所有文章");
        let store = ctx.data::<DataStore>()?;
        let posts = store.posts.read().await;
        Ok(posts.values().cloned().collect())
    }
    
    /// 根据ID获取文章
    async fn post(&self, ctx: &Context<'_>, id: ID) -> GraphQLResult<Option<Post>> {
        info!("GraphQL: 查询文章 {}", id);
        let store = ctx.data::<DataStore>()?;
        let posts = store.posts.read().await;
        Ok(posts.get(&id.to_string()).cloned())
    }
    
    /// 根据作者ID获取文章
    async fn posts_by_author(&self, ctx: &Context<'_>, author_id: ID) -> GraphQLResult<Vec<Post>> {
        info!("GraphQL: 查询作者 {} 的文章", author_id);
        let store = ctx.data::<DataStore>()?;
        let posts = store.posts.read().await;
        
        let results: Vec<Post> = posts
            .values()
            .filter(|post| post.author_id == author_id)
            .cloned()
            .collect();
        
        Ok(results)
    }
    
    /// 搜索文章
    async fn search_posts(
        &self,
        ctx: &Context<'_>,
        input: SearchInput,
    ) -> GraphQLResult<Vec<Post>> {
        info!("GraphQL: 搜索文章 - {}", input.query);
        let store = ctx.data::<DataStore>()?;
        let posts = store.posts.read().await;
        
        let results: Vec<Post> = posts
            .values()
            .filter(|post| {
                post.title.contains(&input.query) || post.content.contains(&input.query)
            })
            .cloned()
            .collect();
        
        Ok(results)
    }
    
    /// 获取所有评论
    async fn comments(&self, ctx: &Context<'_>) -> GraphQLResult<Vec<Comment>> {
        info!("GraphQL: 查询所有评论");
        let store = ctx.data::<DataStore>()?;
        let comments = store.comments.read().await;
        Ok(comments.values().cloned().collect())
    }
    
    /// 根据文章ID获取评论
    async fn comments_by_post(&self, ctx: &Context<'_>, post_id: ID) -> GraphQLResult<Vec<Comment>> {
        info!("GraphQL: 查询文章 {} 的评论", post_id);
        let store = ctx.data::<DataStore>()?;
        let comments = store.comments.read().await;
        
        let results: Vec<Comment> = comments
            .values()
            .filter(|comment| comment.post_id == post_id)
            .cloned()
            .collect();
        
        Ok(results)
    }
    
    /// 健康检查
    async fn health(&self) -> GraphQLResult<String> {
        info!("GraphQL: 健康检查");
        Ok("healthy".to_string())
    }
    
    /// 版本信息
    async fn version(&self) -> GraphQLResult<String> {
        info!("GraphQL: 版本查询");
        Ok(env!("CARGO_PKG_VERSION").to_string())
    }
}

/// GraphQL 变更根
pub struct MutationRoot;

#[Object]
impl MutationRoot {
    /// 创建用户
    async fn create_user(
        &self,
        ctx: &Context<'_>,
        input: CreateUserInput,
    ) -> GraphQLResult<User> {
        info!("GraphQL: 创建用户 - {}", input.name);
        let store = ctx.data::<DataStore>()?;
        
        let user_id = Uuid::new_v4().to_string();
        let user = User {
            id: ID::from(&user_id),
            name: input.name,
            email: input.email,
            age: input.age,
            created_at: Utc::now(),
            posts: vec![],
            profile: None,
        };
        
        let mut users = store.users.write().await;
        users.insert(user_id, user.clone());
        
        Ok(user)
    }
    
    /// 更新用户
    async fn update_user(
        &self,
        ctx: &Context<'_>,
        id: ID,
        input: CreateUserInput,
    ) -> GraphQLResult<Option<User>> {
        info!("GraphQL: 更新用户 {}", id);
        let store = ctx.data::<DataStore>()?;
        
        let mut users = store.users.write().await;
        if let Some(user) = users.get_mut(&id.to_string()) {
            user.name = input.name;
            user.email = input.email;
            user.age = input.age;
            Ok(Some(user.clone()))
        } else {
            Ok(None)
        }
    }
    
    /// 删除用户
    async fn delete_user(&self, ctx: &Context<'_>, id: ID) -> GraphQLResult<bool> {
        info!("GraphQL: 删除用户 {}", id);
        let store = ctx.data::<DataStore>()?;
        
        let mut users = store.users.write().await;
        Ok(users.remove(&id.to_string()).is_some())
    }
    
    /// 创建文章
    async fn create_post(
        &self,
        ctx: &Context<'_>,
        input: CreatePostInput,
    ) -> GraphQLResult<Post> {
        info!("GraphQL: 创建文章 - {}", input.title);
        let store = ctx.data::<DataStore>()?;
        
        let post_id = Uuid::new_v4().to_string();
        let post = Post {
            id: ID::from(&post_id),
            title: input.title,
            content: input.content,
            author_id: input.author_id,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            tags: input.tags,
            comments: vec![],
        };
        
        let mut posts = store.posts.write().await;
        posts.insert(post_id, post.clone());
        
        Ok(post)
    }
    
    /// 创建评论
    async fn create_comment(
        &self,
        ctx: &Context<'_>,
        input: CreateCommentInput,
    ) -> GraphQLResult<Comment> {
        info!("GraphQL: 创建评论");
        let store = ctx.data::<DataStore>()?;
        
        let comment_id = Uuid::new_v4().to_string();
        let comment = Comment {
            id: ID::from(&comment_id),
            content: input.content,
            author_id: input.author_id,
            post_id: input.post_id,
            created_at: Utc::now(),
        };
        
        let mut comments = store.comments.write().await;
        comments.insert(comment_id, comment.clone());
        
        Ok(comment)
    }
}

/// GraphQL 订阅根
pub struct SubscriptionRoot;

#[Subscription]
impl SubscriptionRoot {
    /// 用户创建订阅
    async fn user_created(&self) -> impl async_stream::Stream<Item = User> {
        async_stream::stream! {
            loop {
                tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
                // 模拟新用户创建事件
                let user = User {
                    id: ID::from(Uuid::new_v4().to_string()),
                    name: "New User".to_string(),
                    email: "newuser@example.com".to_string(),
                    age: Some(25),
                    created_at: Utc::now(),
                    posts: vec![],
                    profile: None,
                };
                yield user;
            }
        }
    }
    
    /// 文章创建订阅
    async fn post_created(&self) -> impl async_stream::Stream<Item = Post> {
        async_stream::stream! {
            loop {
                tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
                // 模拟新文章创建事件
                let post = Post {
                    id: ID::from(Uuid::new_v4().to_string()),
                    title: "New Post".to_string(),
                    content: "This is a new post content...".to_string(),
                    author_id: ID::from("user-1"),
                    created_at: Utc::now(),
                    updated_at: Utc::now(),
                    tags: vec!["new".to_string()],
                    comments: vec![],
                };
                yield post;
            }
        }
    }
}

/// GraphQL 处理器
#[handler]
async fn graphql_handler(
    req: Json<GraphQLRequest>,
    data: poem::web::Data<&Schema<QueryRoot, MutationRoot, SubscriptionRoot>>,
) -> Json<GraphQLResponse> {
    Json(data.execute(req.0).await.into())
}

/// 创建 GraphQL Schema
fn create_schema() -> Schema<QueryRoot, MutationRoot, SubscriptionRoot> {
    let store = DataStore::new();
    Schema::build(QueryRoot, MutationRoot, SubscriptionRoot)
        .data(store)
        .finish()
}

/// 创建路由
fn create_routes() -> Route {
    let schema = create_schema();
    Route::new()
        .at("/graphql", post(graphql_handler))
        .at("/graphiql", async_graphql_poem::GraphiQLEndpoint::new("/graphql"))
        .at("/playground", async_graphql_poem::GraphQLPlaygroundEndpoint::new("/graphql"))
        .data(schema)
        .with(Tracing)
}

/// 主函数
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 GraphQL 微服务演示");
    println!("================================");
    
    // 创建路由
    let app = create_routes();
    
    // 启动服务器
    let listener = TcpListener::bind("127.0.0.1:3003");
    let server = Server::new(listener);
    
    println!("📡 服务器启动在 http://127.0.0.1:3003");
    println!("📋 可用的端点:");
    println!("  POST   /graphql           - GraphQL API");
    println!("  GET    /graphiql          - GraphiQL 界面");
    println!("  GET    /playground        - GraphQL Playground");
    println!();
    println!("🔧 测试查询:");
    println!("  query {{");
    println!("    users {{");
    println!("      id");
    println!("      name");
    println!("      email");
    println!("      posts {{");
    println!("        title");
    println!("        content");
    println!("      }}");
    println!("    }}");
    println!("  }}");
    println!();
    println!("🔧 测试变更:");
    println!("  mutation {{");
    println!("    createUser(input: {{");
    println!("      name: \"Charlie\"");
    println!("      email: \"charlie@example.com\"");
    println!("      age: 28");
    println!("    }}) {{");
    println!("      id");
    println!("      name");
    println!("      email");
    println!("    }}");
    println!("  }}");
    println!();
    
    // 运行服务器
    server.run(app).await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_create_schema() {
        let schema = create_schema();
        assert!(!schema.sdl().is_empty());
    }
    
    #[tokio::test]
    async fn test_query_users() {
        let schema = create_schema();
        let query = r#"
            query {
                users {
                    id
                    name
                    email
                }
            }
        "#;
        
        let result = schema.execute(query).await;
        assert!(result.errors.is_empty());
    }
    
    #[tokio::test]
    async fn test_mutation_create_user() {
        let schema = create_schema();
        let mutation = r#"
            mutation {
                createUser(input: {
                    name: "Test User"
                    email: "test@example.com"
                    age: 25
                }) {
                    id
                    name
                    email
                }
            }
        "#;
        
        let result = schema.execute(mutation).await;
        assert!(result.errors.is_empty());
    }
}
