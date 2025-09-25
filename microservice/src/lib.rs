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
pub mod rust_190_advanced;
pub mod rust_190_enhanced;
pub mod rust_190_features;
pub mod rust_190_optimized;

// 现代微服务框架模块
pub mod modern_frameworks;

// 高级 AI/ML 集成模块
#[cfg(feature = "with-ai-ml")]
pub mod ai_ml_advanced;

// 高级 GraphQL 生态系统模块
#[cfg(feature = "with-graphql")]
pub mod graphql_advanced;

// 高级微服务模式模块
pub mod advanced_microservice_architecture;
pub mod advanced_patterns;

// 高级安全特性模块
// pub mod security_advanced; // 暂时注释掉，避免重复定义

// 混沌工程模块
pub mod chaos_engineering;

// 自动扩缩容模块
pub mod auto_scaling;

// 多云支持模块
pub mod multi_cloud;

// 性能优化模块
pub mod performance_advanced;
pub mod performance_optimization;

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
        AsyncIterator, AsyncService, CircuitBreaker, HealthStatus, LoadBalancer, OrderService,
        ProductService, RetryPolicy, ServiceFactory, ServiceInfo, ServiceMonitor, ServiceRegistry,
        ServiceRequest, ServiceResponse, UserService,
    };

    // Rust 1.90 增强特性预导入
    pub use crate::rust_190_enhanced::{
        AdvancedDataProcessor, CircuitBreaker as EnhancedCircuitBreaker, EnhancedAsyncIterator,
        EnhancedHealthStatus, EnhancedMicroService, EnhancedServiceError, EnhancedServiceImpl,
        EnhancedServiceRequest, EnhancedServiceResponse, HealthState, Priority, RateLimiter,
        RequestStream, ResponseStatus, ServiceConfig, ServiceFactory as EnhancedServiceFactory,
        ServiceMetrics, ServiceRegistry as EnhancedServiceRegistry,
    };

    // 现代微服务框架预导入
    pub use crate::modern_frameworks::{
        FrameworkComparator, FrameworkFactory, FrameworkMetrics,
        HealthStatus as FrameworkHealthStatus, ModernFramework, PerformanceMetrics,
    };

    // 高级 AI/ML 预导入
    #[cfg(feature = "with-ai-ml")]
    pub use crate::ai_ml_advanced::{
        AIMLConfig, AIMLMetrics, AIMLRequest, AIMLResponse, AIMLResult, AIMLServiceFactory,
        AdvancedAIMLService, ImageTask, TextTask,
    };

    // 高级 GraphQL 预导入
    #[cfg(feature = "with-graphql")]
    pub use crate::graphql_advanced::{
        DataLoader, DataStore, GraphQLConfig, GraphQLMetrics, GraphQLService,
        GraphQLServiceFactory, MutationRoot, Order, Product, QueryRoot, SearchInput,
        SubscriptionRoot, User, UserInput, UserUpdateInput,
    };

    // 高级微服务模式预导入
    pub use crate::advanced_patterns::{
        AdvancedPatternsService, AdvancedPatternsServiceFactory, AggregateRoot, Command,
        CommandHandler, CreateUserCommand, DomainEvent, EventHandler, EventStore, GetUserQuery,
        OrderSaga, Query, QueryHandler, SagaCoordinator, SagaStep, SearchUsersQuery,
        UpdateUserCommand, UserAggregate, UserCommandHandler, UserCreatedEvent, UserQueryHandler,
        UserReadModel, UserReadModelStore, UserUpdatedEvent,
    };

    // 高级微服务架构预导入（使用别名以避免与 advanced_patterns 冲突）
    pub use crate::advanced_microservice_architecture::{
        AggregateRoot as ArchAggregateRoot, ArchitectureError as ArchError,
        AutoScaling as ArchAutoScaling, ChaosEngineering as ArchChaosEngineering,
        ChaosExperiment as ArchChaosExperiment, Command as ArchCommand,
        CommandHandler as ArchCommandHandler, CpuScaler as ArchCpuScaler,
        DomainEvent as ArchDomainEvent, EventHandler as ArchEventHandler,
        EventStore as ArchEventStore, ExperimentResults as ArchExperimentResults,
        ExperimentStatus as ArchExperimentStatus, FaultInjector as ArchFaultInjector,
        FaultType as ArchFaultType, GetUserQuery as ArchGetUserQuery,
        InMemoryEventStore as ArchInMemoryEventStore,
        LatencyFaultInjector as ArchLatencyFaultInjector, MetricValue as ArchMetricValue,
        OrderSaga as ArchOrderSaga, Query as ArchQuery, QueryHandler as ArchQueryHandler,
        Saga as ArchSaga, SagaCoordinator as ArchSagaCoordinator, SagaStep as ArchSagaStep,
        SagaStepStatus as ArchSagaStepStatus, Scaler as ArchScaler,
        ScalingAction as ArchScalingAction, ScalingActionType as ArchScalingActionType,
        ScalingEvent as ArchScalingEvent, ScalingType as ArchScalingType, Severity as ArchSeverity,
        SystemStability as ArchSystemStability, UserAggregate as ArchUserAggregate,
        UserCommand as ArchUserCommand, UserCommandHandler as ArchUserCommandHandler,
        UserEvent as ArchUserEvent, UserQueryHandler as ArchUserQueryHandler,
        UserStatus as ArchUserStatus,
    };

    // 高级安全特性预导入
    pub use crate::security_advanced::{
        AccessControlPolicy, AccessEffect, AccessToken, AdvancedJWTClaims, AdvancedSecurityManager,
        AdvancedSecurityService, AuditResult, Certificate, EventResult, EventType, JwtPayload,
        JwtPayload as JwtClaims, Permission, PermissionLevel, ResourceType, Role,
        SecurityAuditEvent, SecurityConfig, SecurityEvent, SecurityPolicy, SecurityRule, User,
        UserIdentity, ZeroTrustPolicy,
    };

    // 混沌工程预导入
    pub use crate::chaos_engineering::{
        AdvancedChaosEngineeringService, ChaosConfig, ChaosEngineeringServiceFactory,
        ChaosExperiment, ChaosMetrics, ChaosMonkey, ExperimentResults, ExperimentStatus,
        FaultInjector, FaultType, ResilienceTestResults, ResilienceTester, Severity,
        SystemStability,
    };

    // 自动扩缩容预导入
    pub use crate::auto_scaling::{
        AutoScalingService, AutoScalingServiceFactory, CustomMetric, HorizontalScaler, MetricType,
        PredictionDataPoint, PredictionModel, PredictiveScaler, ResourceMetrics, ScalingAction,
        ScalingConfig, ScalingEvent, ScalingStats, ScalingType, VerticalScaler,
    };

    // 多云支持预导入
    pub use crate::multi_cloud::{
        AlibabaCloudService, AwsService, AzureService, CloudConfig, CloudCost, CloudProvider,
        CloudResource, CloudResourceType, GcpService, MultiCloudCostSummary, MultiCloudManager,
        MultiCloudServiceFactory, ResourceStatus,
    };

    // 性能优化预导入
    pub use crate::performance_optimization::{
        BenchmarkConfig, BenchmarkResult, ComprehensiveOptimizationResult,
        ConcurrencyOptimizationConfig, ConcurrencyOptimizationResult, ConcurrencyOptimizer,
        ConcurrencyStats, MemoryOptimizationConfig, MemoryOptimizationResult, MemoryOptimizer,
        MemoryStats, OptimizationResult, PerformanceBenchmarker, PerformanceMetric,
        PerformanceMetricType, PerformanceOptimizationFactory, PerformanceOptimizationManager,
        PerformanceRecommendation, RecommendationPriority,
    };

    // 重新导出常用crate
    pub use serde::{Deserialize, Serialize};
    pub use tokio;
    pub use tracing::{debug, error, info, warn};
}

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");
