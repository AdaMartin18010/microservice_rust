//! # Rust 微服务框架集合
//!
//! 这是一个全面的Rust微服务框架集合，支持多种Web框架、gRPC、服务网格和云原生部署。
//! 结合Rust 1.90的最新语言特性，提供高性能、安全、可扩展的微服务解决方案。
//!
//! ## 主要特性
//!
//! - 🚀 **现代Web框架**: Axum, Actix-Web, Warp, Poem, Salvo
//! - 🌐 **gRPC支持**: Tonic, Volo (字节跳动开源), fusen-rs
//! - 🔧 **服务网格**: 服务发现、负载均衡、熔断器
//! - 📊 **可观测性**: OpenTelemetry, Prometheus, Jaeger
//! - 🗄️ **数据库集成**: SQLx, Diesel, SeaORM
//! - ☸️ **Kubernetes**: 部署和配置管理
//! - 🔐 **安全特性**: JWT, OAuth2, HTTPS, CORS
//! - ⚡ **异步模式**: Actor模型、消息队列、事件驱动
//!
//! ## 快速开始
//!
//! ```rust
//! use c13_microservice::prelude::*;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 启动Axum微服务
//!     let app = axum::Router::new()
//!         .route("/health", axum::routing::get(health_check));
//!     
//!     let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
//!     axum::serve(listener, app).await?;
//!     Ok(())
//! }
//!
//! async fn health_check() -> &'static str {
//!     "OK"
//! }
//! ```

// 核心模块
pub mod config;
pub mod error;
pub mod lib_simple;
pub mod middleware;
pub mod utils;

// Rust 1.90 新特性模块
pub mod rust_190_features;
pub mod rust_190_advanced;
pub mod rust_190_enhanced;

// 现代微服务框架模块
pub mod modern_frameworks;

// 高级 AI/ML 集成模块
#[cfg(feature = "with-ai-ml")]
pub mod ai_ml_advanced;

// 高级 GraphQL 生态系统模块
#[cfg(feature = "with-graphql")]
pub mod graphql_advanced;

// 高级微服务模式模块
pub mod advanced_patterns;
pub mod advanced_microservice_architecture;

// 高级安全特性模块
// pub mod security_advanced; // 暂时注释掉，避免重复定义

// 混沌工程模块
pub mod chaos_engineering;

// 自动扩缩容模块
pub mod auto_scaling;

// 多云支持模块
pub mod multi_cloud;

// 性能优化模块
pub mod performance_optimization;
pub mod performance_advanced;

// 简化微服务模块
pub mod simple_microservice;

// Web框架模块
pub mod actix;
pub mod axum;
pub mod tide;
pub mod warp;

// 最新微服务框架模块
#[cfg(feature = "with-poem")]
pub mod poem;
// #[cfg(feature = "with-salvo")]
// pub mod salvo;  // 暂时禁用
#[cfg(feature = "with-volo")]
pub mod volo_advanced;
// #[cfg(feature = "with-fusen")]
// pub mod fusen;  // 暂时禁用
// #[cfg(feature = "with-spring-rs")]
// pub mod spring_rs;  // 暂时禁用

// gRPC和RPC模块
pub mod grpc;
pub mod volo;

// 服务网格模块 - 暂时注释掉
// pub mod service_mesh;
pub mod discovery;
// pub mod load_balancer;
// pub mod circuit_breaker;

// 可观测性模块 - 暂时注释掉
// pub mod observability;
pub mod logging;
pub mod opentelemetry;
// pub mod metrics;
// pub mod tracing;

// 数据库模块 - 暂时注释掉
// pub mod database;
pub mod orm;

// 消息队列模块
pub mod messaging;
// pub mod queue;

// 安全模块
pub mod security;
pub mod security_advanced;

// 服务网格模块
pub mod service_mesh;

// 性能分析模块
pub mod performance;

// Kubernetes和云原生模块 - 暂时注释掉
// pub mod kubernetes;
pub mod kube_rs;

// 异步模式模块 - 暂时注释掉
// pub mod async_patterns;
// pub mod actors;

// 预导入模块
pub mod prelude {
    //! 常用类型和函数的预导入模块

    pub use crate::config::Config;
    pub use crate::discovery::{Consul, Etcd};
    pub use crate::error::{Error, Result};
    pub use crate::messaging::{Kafka, MQTT, NATS, RabbitMQ, Redis};
    pub use crate::middleware::*;
    pub use crate::utils::*;
    
    // Rust 1.90 新特性预导入
    pub use crate::rust_190_features::{
        AsyncService, AsyncIterator, ServiceRegistry, LoadBalancer, 
        CircuitBreaker, RetryPolicy, ServiceMonitor, ServiceFactory,
        ServiceRequest, ServiceResponse, HealthStatus, ServiceInfo,
        UserService, OrderService, ProductService
    };
    
    // Rust 1.90 增强特性预导入
    pub use crate::rust_190_enhanced::{
        EnhancedMicroService, EnhancedAsyncIterator, EnhancedServiceImpl,
        EnhancedServiceRequest, EnhancedServiceResponse, EnhancedHealthStatus,
        ServiceRegistry as EnhancedServiceRegistry, ServiceFactory as EnhancedServiceFactory,
        ServiceConfig, CircuitBreaker as EnhancedCircuitBreaker, RateLimiter,
        RequestStream, AdvancedDataProcessor, Priority, ResponseStatus,
        HealthState, ServiceMetrics, EnhancedServiceError
    };
    
    // 现代微服务框架预导入
    pub use crate::modern_frameworks::{
        ModernFramework, FrameworkFactory, FrameworkComparator,
        HealthStatus as FrameworkHealthStatus, FrameworkMetrics, PerformanceMetrics
    };
    
    // 高级 AI/ML 预导入
    #[cfg(feature = "with-ai-ml")]
    pub use crate::ai_ml_advanced::{
        AdvancedAIMLService, AIMLConfig, AIMLRequest, AIMLResponse, AIMLResult,
        TextTask, ImageTask, AIMLServiceFactory, AIMLMetrics
    };
    
    // 高级 GraphQL 预导入
    #[cfg(feature = "with-graphql")]
    pub use crate::graphql_advanced::{
        GraphQLService, GraphQLConfig, GraphQLServiceFactory, GraphQLMetrics,
        User, Product, Order, UserInput, UserUpdateInput, SearchInput,
        DataStore, DataLoader, QueryRoot, MutationRoot, SubscriptionRoot
    };
    
    // 高级微服务模式预导入
    pub use crate::advanced_patterns::{
        AdvancedPatternsService, AdvancedPatternsServiceFactory,
        Command, Query, DomainEvent, AggregateRoot, CommandHandler, QueryHandler, EventHandler,
        CreateUserCommand, UpdateUserCommand, GetUserQuery, SearchUsersQuery,
        UserCreatedEvent, UserUpdatedEvent, UserAggregate, UserReadModel,
        UserCommandHandler, UserQueryHandler, UserReadModelStore,
        EventStore, SagaCoordinator, SagaStep, OrderSaga
    };
    
    // 高级微服务架构预导入（使用别名以避免与 advanced_patterns 冲突）
    pub use crate::advanced_microservice_architecture::{
        ArchitectureError as ArchError,
        DomainEvent as ArchDomainEvent,
        Command as ArchCommand,
        Query as ArchQuery,
        AggregateRoot as ArchAggregateRoot,
        CommandHandler as ArchCommandHandler,
        QueryHandler as ArchQueryHandler,
        EventHandler as ArchEventHandler,
        EventStore as ArchEventStore,
        InMemoryEventStore as ArchInMemoryEventStore,
        UserAggregate as ArchUserAggregate,
        UserCommand as ArchUserCommand,
        UserEvent as ArchUserEvent,
        UserStatus as ArchUserStatus,
        UserCommandHandler as ArchUserCommandHandler,
        UserQueryHandler as ArchUserQueryHandler,
        GetUserQuery as ArchGetUserQuery,
        SagaCoordinator as ArchSagaCoordinator,
        Saga as ArchSaga,
        SagaStep as ArchSagaStep,
        SagaStepStatus as ArchSagaStepStatus,
        OrderSaga as ArchOrderSaga,
        ChaosEngineering as ArchChaosEngineering,
        FaultInjector as ArchFaultInjector,
        FaultType as ArchFaultType,
        ChaosExperiment as ArchChaosExperiment,
        Severity as ArchSeverity,
        ExperimentStatus as ArchExperimentStatus,
        ExperimentResults as ArchExperimentResults,
        SystemStability as ArchSystemStability,
        LatencyFaultInjector as ArchLatencyFaultInjector,
        AutoScaling as ArchAutoScaling,
        Scaler as ArchScaler,
        ScalingType as ArchScalingType,
        ScalingAction as ArchScalingAction,
        ScalingActionType as ArchScalingActionType,
        ScalingEvent as ArchScalingEvent,
        MetricValue as ArchMetricValue,
        CpuScaler as ArchCpuScaler
    };
    
    // 高级安全特性预导入
    pub use crate::security_advanced::{
        AdvancedSecurityService, AdvancedSecurityManager, SecurityConfig,
        User, Role, Permission, AccessToken, JwtPayload, SecurityPolicy, SecurityEvent,
        Certificate, SecurityRule, EventType, EventResult, JwtPayload as JwtClaims,
        ZeroTrustPolicy, UserIdentity, AdvancedJWTClaims, PermissionLevel, ResourceType,
        AccessControlPolicy, AccessEffect, SecurityAuditEvent, AuditResult
    };
    
    // 混沌工程预导入
    pub use crate::chaos_engineering::{
        AdvancedChaosEngineeringService, ChaosEngineeringServiceFactory, ChaosConfig,
        FaultInjector, ChaosMonkey, ResilienceTester, ChaosExperiment, ExperimentResults,
        FaultType, Severity, ExperimentStatus, SystemStability, ChaosMetrics,
        ResilienceTestResults
    };
    
    // 自动扩缩容预导入
    pub use crate::auto_scaling::{
        AutoScalingService, AutoScalingServiceFactory, ScalingConfig,
        HorizontalScaler, VerticalScaler, PredictiveScaler, ScalingEvent, ScalingAction,
        ScalingType, ResourceMetrics, PredictionDataPoint, CustomMetric, MetricType,
        ScalingStats, PredictionModel
    };
    
    // 多云支持预导入
    pub use crate::multi_cloud::{
        MultiCloudManager, MultiCloudServiceFactory, CloudConfig, CloudProvider,
        AwsService, AzureService, GcpService, AlibabaCloudService,
        CloudResource, CloudResourceType, ResourceStatus, CloudCost,
        MultiCloudCostSummary
    };
    
    // 性能优化预导入
    pub use crate::performance_optimization::{
        PerformanceOptimizationManager, PerformanceOptimizationFactory,
        PerformanceBenchmarker, MemoryOptimizer, ConcurrencyOptimizer,
        BenchmarkConfig, BenchmarkResult, MemoryOptimizationConfig, MemoryStats,
        ConcurrencyOptimizationConfig, ConcurrencyStats, PerformanceMetric,
        PerformanceMetricType, ComprehensiveOptimizationResult, OptimizationResult,
        MemoryOptimizationResult, ConcurrencyOptimizationResult, PerformanceRecommendation,
        RecommendationPriority
    };

    // 重新导出常用crate
    pub use serde::{Deserialize, Serialize};
    pub use tokio;
    pub use tracing::{debug, error, info, warn};
}

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");
