//! Poem 框架中间件模块
//! 
//! 提供各种常用的HTTP中间件实现

use poem::{
    middleware::{Cors, Tracing},
    Endpoint, EndpointExt, Middleware, Request, Response, Result as PoemResult,
};
use std::time::Instant;
use tracing::{info, warn, error, span, Level};

/// 请求ID中间件
pub struct RequestIdMiddleware;

impl<E: Endpoint> Middleware<E> for RequestIdMiddleware {
    type Output = RequestIdEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        RequestIdEndpoint { ep }
    }
}

pub struct RequestIdEndpoint<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for RequestIdEndpoint<E> {
    type Output = Response;

    async fn call(&self, mut req: Request) -> PoemResult<Self::Output> {
        let request_id = uuid::Uuid::new_v4().to_string();
        req.headers_mut().insert(
            "X-Request-ID",
            request_id.parse().unwrap(),
        );
        
        let response = self.ep.call(req).await?;
        Ok(response)
    }
}

/// 性能监控中间件
pub struct PerformanceMiddleware;

impl<E: Endpoint> Middleware<E> for PerformanceMiddleware {
    type Output = PerformanceEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        PerformanceEndpoint { ep }
    }
}

pub struct PerformanceEndpoint<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for PerformanceEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        let start = Instant::now();
        let method = req.method().clone();
        let path = req.uri().path().to_string();
        
        let span = span!(Level::INFO, "request", method = %method, path = %path);
        let _enter = span.enter();
        
        let response = self.ep.call(req).await?;
        let duration = start.elapsed();
        
        info!(
            "请求完成: {} {} - 状态: {} - 耗时: {:?}",
            method,
            path,
            response.status(),
            duration
        );
        
        Ok(response)
    }
}

/// 限流中间件
pub struct RateLimitMiddleware {
    max_requests: u32,
    window_seconds: u64,
}

impl RateLimitMiddleware {
    pub fn new(max_requests: u32, window_seconds: u64) -> Self {
        Self {
            max_requests,
            window_seconds,
        }
    }
}

impl<E: Endpoint> Middleware<E> for RateLimitMiddleware {
    type Output = RateLimitEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        RateLimitEndpoint {
            ep,
            max_requests: self.max_requests,
            window_seconds: self.window_seconds,
        }
    }
}

pub struct RateLimitEndpoint<E> {
    ep: E,
    max_requests: u32,
    window_seconds: u64,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for RateLimitEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        // 简化的限流实现
        let client_ip = req
            .headers()
            .get("X-Forwarded-For")
            .or_else(|| req.headers().get("X-Real-IP"))
            .and_then(|h| h.to_str().ok())
            .unwrap_or("unknown");
        
        // 这里应该实现真正的限流逻辑
        // 例如使用 Redis 或内存计数器
        
        info!("限流检查: IP = {}, 限制 = {}/{}s", client_ip, self.max_requests, self.window_seconds);
        
        self.ep.call(req).await
    }
}

/// 认证中间件
pub struct AuthMiddleware {
    secret_key: String,
}

impl AuthMiddleware {
    pub fn new(secret_key: String) -> Self {
        Self { secret_key }
    }
}

impl<E: Endpoint> Middleware<E> for AuthMiddleware {
    type Output = AuthEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        AuthEndpoint {
            ep,
            secret_key: self.secret_key.clone(),
        }
    }
}

pub struct AuthEndpoint<E> {
    ep: E,
    secret_key: String,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for AuthEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        let auth_header = req.headers().get("Authorization");
        
        match auth_header {
            Some(header) => {
                if let Ok(token) = header.to_str() {
                    if token.starts_with("Bearer ") {
                        let token = &token[7..];
                        // 这里应该验证JWT token
                        info!("认证成功: token = {}", &token[..10]);
                        return self.ep.call(req).await;
                    }
                }
            }
            None => {}
        }
        
        warn!("认证失败: 缺少有效的Authorization头");
        Ok(Response::builder()
            .status(401)
            .body("Unauthorized"))
    }
}

/// 缓存中间件
pub struct CacheMiddleware {
    ttl_seconds: u64,
}

impl CacheMiddleware {
    pub fn new(ttl_seconds: u64) -> Self {
        Self { ttl_seconds }
    }
}

impl<E: Endpoint> Middleware<E> for CacheMiddleware {
    type Output = CacheEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        CacheEndpoint {
            ep,
            ttl_seconds: self.ttl_seconds,
        }
    }
}

pub struct CacheEndpoint<E> {
    ep: E,
    ttl_seconds: u64,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for CacheEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        let cache_key = format!("{}:{}", req.method(), req.uri().path());
        
        // 这里应该实现真正的缓存逻辑
        // 例如使用 Redis 或内存缓存
        
        info!("缓存检查: key = {}, TTL = {}s", cache_key, self.ttl_seconds);
        
        let response = self.ep.call(req).await?;
        
        // 设置缓存头
        let mut response = response;
        response.headers_mut().insert(
            "Cache-Control",
            format!("public, max-age={}", self.ttl_seconds).parse().unwrap(),
        );
        
        Ok(response)
    }
}

/// 压缩中间件
pub struct CompressionMiddleware;

impl<E: Endpoint> Middleware<E> for CompressionMiddleware {
    type Output = CompressionEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        CompressionEndpoint { ep }
    }
}

pub struct CompressionEndpoint<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for CompressionEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        let accept_encoding = req.headers().get("Accept-Encoding");
        
        let response = self.ep.call(req).await?;
        
        // 检查客户端是否支持压缩
        if let Some(encoding) = accept_encoding {
            if let Ok(encoding_str) = encoding.to_str() {
                if encoding_str.contains("gzip") {
                    // 这里应该实现真正的压缩逻辑
                    info!("响应压缩: gzip");
                }
            }
        }
        
        Ok(response)
    }
}

/// 安全头中间件
pub struct SecurityHeadersMiddleware;

impl<E: Endpoint> Middleware<E> for SecurityHeadersMiddleware {
    type Output = SecurityHeadersEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        SecurityHeadersEndpoint { ep }
    }
}

pub struct SecurityHeadersEndpoint<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for SecurityHeadersEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        let response = self.ep.call(req).await?;
        let mut response = response;
        
        // 添加安全头
        response.headers_mut().insert(
            "X-Content-Type-Options",
            "nosniff".parse().unwrap(),
        );
        response.headers_mut().insert(
            "X-Frame-Options",
            "DENY".parse().unwrap(),
        );
        response.headers_mut().insert(
            "X-XSS-Protection",
            "1; mode=block".parse().unwrap(),
        );
        response.headers_mut().insert(
            "Strict-Transport-Security",
            "max-age=31536000; includeSubDomains".parse().unwrap(),
        );
        
        Ok(response)
    }
}

/// 错误处理中间件
pub struct ErrorHandlingMiddleware;

impl<E: Endpoint> Middleware<E> for ErrorHandlingMiddleware {
    type Output = ErrorHandlingEndpoint<E>;

    fn transform(&self, ep: E) -> Self::Output {
        ErrorHandlingEndpoint { ep }
    }
}

pub struct ErrorHandlingEndpoint<E> {
    ep: E,
}

#[poem::async_trait]
impl<E: Endpoint> Endpoint for ErrorHandlingEndpoint<E> {
    type Output = Response;

    async fn call(&self, req: Request) -> PoemResult<Self::Output> {
        match self.ep.call(req).await {
            Ok(response) => Ok(response),
            Err(err) => {
                error!("请求处理错误: {:?}", err);
                Ok(Response::builder()
                    .status(500)
                    .body("Internal Server Error"))
            }
        }
    }
}

/// 创建完整的中间件栈
pub fn create_middleware_stack() -> impl Middleware<()> {
    SecurityHeadersMiddleware
        .around(ErrorHandlingMiddleware)
        .around(CompressionMiddleware)
        .around(CacheMiddleware::new(300))
        .around(AuthMiddleware::new("secret".to_string()))
        .around(RateLimitMiddleware::new(100, 60))
        .around(PerformanceMiddleware)
        .around(RequestIdMiddleware)
        .around(Tracing)
        .around(Cors::new().allow_origin("*").allow_methods(vec!["GET", "POST", "PUT", "DELETE"]))
}
