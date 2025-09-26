//! Salvo 微服务框架演示（简化版本）
//!
//! 本示例展示了如何使用 Salvo 框架的概念构建微服务
//! 注意：这是一个简化版本，不依赖外部 salvo 库

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;

/// 产品数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Product {
    pub id: u64,
    pub name: String,
    pub description: String,
    pub price: f64,
    pub category: String,
    pub stock: i32,
    pub created_at: String,
}

/// 创建产品请求
#[derive(Debug, Serialize, Deserialize)]
pub struct CreateProductRequest {
    pub name: String,
    pub description: String,
    pub price: f64,
    pub category: String,
    pub stock: i32,
}

/// 更新产品请求
#[derive(Debug, Serialize, Deserialize, Default)]
pub struct UpdateProductRequest {
    pub name: Option<String>,
    pub description: Option<String>,
    pub price: Option<f64>,
    pub category: Option<String>,
    pub stock: Option<i32>,
}

/// 搜索查询
#[derive(Debug, Serialize, Deserialize)]
pub struct SearchQuery {
    pub q: Option<String>,
    pub category: Option<String>,
    pub min_price: Option<f64>,
    pub max_price: Option<f64>,
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

/// 简化的 Salvo 风格服务
#[derive(Debug)]
pub struct SalvoStyleService {
    products: Arc<RwLock<HashMap<u64, Product>>>,
    next_id: Arc<RwLock<u64>>,
}

impl SalvoStyleService {
    pub fn new() -> Self {
        let mut products = HashMap::new();

        // 添加一些示例产品
        let sample_products = vec![
            Product {
                id: 1,
                name: "笔记本电脑".to_string(),
                description: "高性能游戏笔记本".to_string(),
                price: 8999.99,
                category: "电子产品".to_string(),
                stock: 50,
                created_at: chrono::Utc::now().to_rfc3339(),
            },
            Product {
                id: 2,
                name: "智能手机".to_string(),
                description: "最新款智能手机".to_string(),
                price: 3999.99,
                category: "电子产品".to_string(),
                stock: 100,
                created_at: chrono::Utc::now().to_rfc3339(),
            },
            Product {
                id: 3,
                name: "咖啡杯".to_string(),
                description: "陶瓷咖啡杯".to_string(),
                price: 29.99,
                category: "家居用品".to_string(),
                stock: 200,
                created_at: chrono::Utc::now().to_rfc3339(),
            },
        ];

        for product in sample_products {
            products.insert(product.id, product);
        }

        Self {
            products: Arc::new(RwLock::new(products)),
            next_id: Arc::new(RwLock::new(4)),
        }
    }

    /// 获取所有产品
    pub async fn get_products(&self) -> Result<ApiResponse<Vec<Product>>> {
        info!("获取所有产品");

        let products = self.products.read().await;
        let product_list: Vec<Product> = products.values().cloned().collect();

        Ok(ApiResponse::success(product_list))
    }

    /// 获取特定产品
    pub async fn get_product(&self, id: u64) -> Result<ApiResponse<Product>> {
        info!("获取产品: {}", id);

        let products = self.products.read().await;
        match products.get(&id) {
            Some(product) => Ok(ApiResponse::success(product.clone())),
            None => Ok(ApiResponse::error(format!("产品 {} 未找到", id))),
        }
    }

    /// 按类别获取产品
    pub async fn get_products_by_category(
        &self,
        category: &str,
    ) -> Result<ApiResponse<Vec<Product>>> {
        info!("按类别获取产品: {}", category);

        let products = self.products.read().await;
        let filtered_products: Vec<Product> = products
            .values()
            .filter(|product| product.category == category)
            .cloned()
            .collect();

        Ok(ApiResponse::success(filtered_products))
    }

    /// 创建产品
    pub async fn create_product(
        &self,
        request: CreateProductRequest,
    ) -> Result<ApiResponse<Product>> {
        info!("创建产品: {}", request.name);

        if request.name.is_empty() || request.price < 0.0 {
            return Ok(ApiResponse::error(
                "产品名称不能为空且价格不能为负数".to_string(),
            ));
        }

        let mut next_id = self.next_id.write().await;
        let id = *next_id;
        *next_id += 1;

        let product = Product {
            id,
            name: request.name.clone(),
            description: request.description.clone(),
            price: request.price,
            category: request.category.clone(),
            stock: request.stock,
            created_at: chrono::Utc::now().to_rfc3339(),
        };

        self.products.write().await.insert(id, product.clone());

        Ok(ApiResponse::success(product))
    }

    /// 更新产品
    pub async fn update_product(
        &self,
        id: u64,
        request: UpdateProductRequest,
    ) -> Result<ApiResponse<Product>> {
        info!("更新产品: {}", id);

        let mut products = self.products.write().await;
        match products.get_mut(&id) {
            Some(product) => {
                if let Some(name) = request.name {
                    product.name = name;
                }
                if let Some(description) = request.description {
                    product.description = description;
                }
                if let Some(price) = request.price {
                    product.price = price;
                }
                if let Some(category) = request.category {
                    product.category = category;
                }
                if let Some(stock) = request.stock {
                    product.stock = stock;
                }
                Ok(ApiResponse::success(product.clone()))
            }
            None => Ok(ApiResponse::error(format!("产品 {} 未找到", id))),
        }
    }

    /// 删除产品
    pub async fn delete_product(&self, id: u64) -> Result<ApiResponse<String>> {
        info!("删除产品: {}", id);

        let mut products = self.products.write().await;
        match products.remove(&id) {
            Some(_) => Ok(ApiResponse::success(format!("产品 {} 已删除", id))),
            None => Ok(ApiResponse::error(format!("产品 {} 未找到", id))),
        }
    }

    /// 更新库存
    pub async fn update_stock(&self, id: u64, stock_change: i32) -> Result<ApiResponse<Product>> {
        info!("更新产品 {} 库存: {}", id, stock_change);

        let mut products = self.products.write().await;
        match products.get_mut(&id) {
            Some(product) => {
                product.stock += stock_change;
                if product.stock < 0 {
                    product.stock = 0;
                }
                Ok(ApiResponse::success(product.clone()))
            }
            None => Ok(ApiResponse::error(format!("产品 {} 未找到", id))),
        }
    }

    /// 搜索产品
    pub async fn search_products(&self, query: SearchQuery) -> Result<ApiResponse<Vec<Product>>> {
        info!("搜索产品: {:?}", query);

        let products = self.products.read().await;
        let mut filtered_products: Vec<Product> = products.values().cloned().collect();

        // 按名称搜索
        if let Some(q) = &query.q {
            if !q.is_empty() {
                filtered_products
                    .retain(|product| product.name.contains(q) || product.description.contains(q));
            }
        }

        // 按类别筛选
        if let Some(category) = &query.category {
            filtered_products.retain(|product| product.category == *category);
        }

        // 按价格范围筛选
        if let Some(min_price) = query.min_price {
            filtered_products.retain(|product| product.price >= min_price);
        }
        if let Some(max_price) = query.max_price {
            filtered_products.retain(|product| product.price <= max_price);
        }

        Ok(ApiResponse::success(filtered_products))
    }

    /// 获取健康状态
    pub async fn health_check(&self) -> Result<ApiResponse<HashMap<String, String>>> {
        info!("健康检查");

        let mut status = HashMap::new();
        status.insert("status".to_string(), "healthy".to_string());
        status.insert("timestamp".to_string(), chrono::Utc::now().to_rfc3339());
        status.insert("version".to_string(), "1.0.0".to_string());

        Ok(ApiResponse::success(status))
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> Result<ApiResponse<HashMap<String, u64>>> {
        info!("获取指标");

        let products = self.products.read().await;
        let mut metrics = HashMap::new();
        metrics.insert("total_products".to_string(), products.len() as u64);

        let total_stock: i32 = products.values().map(|p| p.stock).sum();
        metrics.insert("total_stock".to_string(), total_stock as u64);

        Ok(ApiResponse::success(metrics))
    }
}

/// 简化的 HTTP 请求处理器
#[derive(Debug)]
pub struct HttpHandler {
    service: SalvoStyleService,
}

impl HttpHandler {
    pub fn new() -> Self {
        Self {
            service: SalvoStyleService::new(),
        }
    }

    /// 模拟 HTTP GET 请求
    pub async fn handle_get(&self, path: &str) -> Result<String> {
        match path {
            "/products" => {
                let response = self.service.get_products().await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            path if path.starts_with("/products/") => {
                let id_str = &path[10..]; // 移除 "/products/"
                if let Ok(id) = id_str.parse::<u64>() {
                    let response = self.service.get_product(id).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的产品ID".to_string()),
                    )?)
                }
            }
            path if path.starts_with("/products/category/") => {
                let category = &path[20..]; // 移除 "/products/category/"
                let response = self.service.get_products_by_category(category).await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            "/health" => {
                let response = self.service.health_check().await?;
                Ok(serde_json::to_string_pretty(&response)?)
            }
            "/metrics" => {
                let response = self.service.get_metrics().await?;
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
            "/products" => {
                let request: CreateProductRequest = serde_json::from_str(body)?;
                let response = self.service.create_product(request).await?;
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
            path if path.starts_with("/products/") && path.ends_with("/stock") => {
                let id_str = path
                    .strip_suffix("/stock")
                    .unwrap()
                    .strip_prefix("/products/")
                    .unwrap();
                if let Ok(id) = id_str.parse::<u64>() {
                    let stock_change: HashMap<String, i32> = serde_json::from_str(body)?;
                    if let Some(change) = stock_change.get("change") {
                        let response = self.service.update_stock(id, *change).await?;
                        Ok(serde_json::to_string_pretty(&response)?)
                    } else {
                        Ok(serde_json::to_string_pretty(
                            &ApiResponse::<String>::error("缺少 change 字段".to_string()),
                        )?)
                    }
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的产品ID".to_string()),
                    )?)
                }
            }
            path if path.starts_with("/products/") => {
                let id_str = &path[10..]; // 移除 "/products/"
                if let Ok(id) = id_str.parse::<u64>() {
                    let request: UpdateProductRequest = serde_json::from_str(body)?;
                    let response = self.service.update_product(id, request).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的产品ID".to_string()),
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
            path if path.starts_with("/products/") => {
                let id_str = &path[10..]; // 移除 "/products/"
                if let Ok(id) = id_str.parse::<u64>() {
                    let response = self.service.delete_product(id).await?;
                    Ok(serde_json::to_string_pretty(&response)?)
                } else {
                    Ok(serde_json::to_string_pretty(
                        &ApiResponse::<String>::error("无效的产品ID".to_string()),
                    )?)
                }
            }
            _ => Ok(serde_json::to_string_pretty(
                &ApiResponse::<String>::error("未找到路径".to_string()),
            )?),
        }
    }

    /// 模拟查询参数处理
    pub async fn handle_search(&self, query_params: &str) -> Result<String> {
        let search_query: SearchQuery = serde_json::from_str(&format!("{{{}}}", query_params))?;
        let response = self.service.search_products(search_query).await?;
        Ok(serde_json::to_string_pretty(&response)?)
    }
}

/// 主函数演示 Salvo 风格的服务
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Salvo 风格微服务演示");
    println!("================================");

    let handler = HttpHandler::new();

    // 演示获取所有产品
    println!("\n📦 获取所有产品:");
    let response = handler.handle_get("/products").await?;
    println!("GET /products: {}", response);

    // 演示获取特定产品
    println!("\n🔍 获取特定产品:");
    let response = handler.handle_get("/products/1").await?;
    println!("GET /products/1: {}", response);

    // 演示按类别获取产品
    println!("\n📂 按类别获取产品:");
    let response = handler.handle_get("/products/category/电子产品").await?;
    println!("GET /products/category/电子产品: {}", response);

    // 演示创建产品
    println!("\n➕ 创建产品:");
    let create_request = CreateProductRequest {
        name: "平板电脑".to_string(),
        description: "高性能平板电脑".to_string(),
        price: 2999.99,
        category: "电子产品".to_string(),
        stock: 30,
    };
    let response = handler
        .handle_post("/products", &serde_json::to_string(&create_request)?)
        .await?;
    println!("POST /products: {}", response);

    // 演示更新产品
    println!("\n✏️  更新产品:");
    let update_request = UpdateProductRequest {
        name: Some("平板电脑（升级版）".to_string()),
        price: Some(3299.99),
        ..Default::default()
    };
    let response = handler
        .handle_put("/products/4", &serde_json::to_string(&update_request)?)
        .await?;
    println!("PUT /products/4: {}", response);

    // 演示更新库存
    println!("\n📊 更新库存:");
    let stock_change = serde_json::json!({"change": -5});
    let response = handler
        .handle_put("/products/4/stock", &stock_change.to_string())
        .await?;
    println!("PUT /products/4/stock: {}", response);

    // 演示搜索产品
    println!("\n🔎 搜索产品:");
    let search_params = r#""q":"电脑","min_price":1000.0"#;
    let response = handler.handle_search(search_params).await?;
    println!("GET /products/search: {}", response);

    // 演示获取健康状态
    println!("\n❤️  健康检查:");
    let response = handler.handle_get("/health").await?;
    println!("GET /health: {}", response);

    // 演示获取指标
    println!("\n📈 获取指标:");
    let response = handler.handle_get("/metrics").await?;
    println!("GET /metrics: {}", response);

    // 演示删除产品
    println!("\n🗑️  删除产品:");
    let response = handler.handle_delete("/products/2").await?;
    println!("DELETE /products/2: {}", response);

    // 演示获取更新后的产品列表
    println!("\n📦 获取更新后的产品列表:");
    let response = handler.handle_get("/products").await?;
    println!("GET /products: {}", response);

    println!("\n✅ Salvo 风格微服务演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- RESTful API 设计");
    println!("- 产品管理功能");
    println!("- 库存管理");
    println!("- 搜索和筛选");
    println!("- 健康检查和指标");
    println!("- JSON 序列化/反序列化");
    println!("- 异步处理");
    println!("- 错误处理");
    println!();
    println!("📚 框架特点:");
    println!("- 高性能异步处理");
    println!("- 类型安全的请求/响应");
    println!("- 中间件支持");
    println!("- 易于扩展");
    println!("- 自动文档生成");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_create_product() {
        let service = SalvoStyleService::new();
        let request = CreateProductRequest {
            name: "测试产品".to_string(),
            description: "测试描述".to_string(),
            price: 99.99,
            category: "测试类别".to_string(),
            stock: 10,
        };

        let response = service.create_product(request).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "测试产品");
    }

    #[tokio::test]
    async fn test_get_product() {
        let service = SalvoStyleService::new();

        let response = service.get_product(1).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "笔记本电脑");
    }

    #[tokio::test]
    async fn test_update_product() {
        let service = SalvoStyleService::new();

        let update_request = UpdateProductRequest {
            name: Some("更新的产品".to_string()),
            price: Some(199.99),
            ..Default::default()
        };

        let response = service.update_product(1, update_request).await.unwrap();
        assert!(response.success);
        assert_eq!(response.data.unwrap().name, "更新的产品");
    }

    #[tokio::test]
    async fn test_delete_product() {
        let service = SalvoStyleService::new();

        let response = service.delete_product(3).await.unwrap();
        assert!(response.success);

        // 验证产品已删除
        let response = service.get_product(3).await.unwrap();
        assert!(!response.success);
    }

    #[tokio::test]
    async fn test_search_products() {
        let service = SalvoStyleService::new();

        let query = SearchQuery {
            q: Some("电脑".to_string()),
            category: None,
            min_price: None,
            max_price: None,
        };

        let response = service.search_products(query).await.unwrap();
        assert!(response.success);
        assert!(!response.data.unwrap().is_empty());
    }
}
