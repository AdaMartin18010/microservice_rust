//! 高级 AI/ML 功能演示
//!
//! 本示例展示了如何使用高级 AI/ML 功能：
//! - 多模态 AI 服务（文本、图像、语音）
//! - 智能推荐系统
//! - 异常检测和监控
//! - 模型管理和版本控制
//! - 实时推理服务

use anyhow::Result;

// 导入我们的高级 AI/ML 模块
#[cfg(feature = "with-ai-ml")]
use microservice::ai_ml_advanced::*;

/// AI/ML 演示管理器
#[cfg(feature = "with-ai-ml")]
pub struct AIMLDemoManager {
    service: AdvancedAIMLService,
}

/// AI/ML 演示管理器（非 AI/ML 特性版本）
#[cfg(not(feature = "with-ai-ml"))]
pub struct AIMLDemoManager {
    // 空结构体，用于非 AI/ML 特性版本
}

impl AIMLDemoManager {
    #[cfg(feature = "with-ai-ml")]
    pub fn new() -> Self {
        let config = AIMLConfig {
            model_cache_size: 20,
            inference_timeout_ms: 10000,
            batch_size: 64,
            enable_gpu: false,
            model_update_interval: 7200, // 2 hours
        };

        let service = AdvancedAIMLService::new(config);

        Self { service }
    }

    #[cfg(not(feature = "with-ai-ml"))]
    pub fn new() -> Self {
        Self {
            // 空结构体，用于非 AI/ML 特性版本
        }
    }

    /// 初始化 AI/ML 服务
    #[cfg(feature = "with-ai-ml")]
    pub async fn initialize(&self) -> Result<()> {
        println!("🤖 初始化 AI/ML 服务...");

        // 注册模拟文本模型
        let text_model = AIMLServiceFactory::create_mock_text_model("bert-base", "1.0.0");
        self.service
            .register_text_model("bert-base".to_string(), text_model)
            .await?;

        println!("✅ 文本模型已注册");

        // 这里可以注册更多模型
        // let image_model = AIMLServiceFactory::create_mock_image_model("resnet50", "1.0.0");
        // self.service.register_image_model("resnet50".to_string(), image_model).await?;

        println!("✅ AI/ML 服务初始化完成");
        Ok(())
    }

    /// 初始化 AI/ML 服务（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn initialize(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过初始化");
        Ok(())
    }

    /// 演示文本分析功能
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_text_analysis(&self) -> Result<()> {
        println!("\n📝 演示文本分析功能:");
        println!("================================");

        let test_texts = vec![
            "这是一个非常好的产品，我非常喜欢！",
            "这个服务太差了，完全不推荐使用。",
            "今天天气不错，适合出门散步。",
            "人工智能技术正在快速发展，改变着我们的生活。",
        ];

        for (i, text) in test_texts.iter().enumerate() {
            println!("\n文本 {}: {}", i + 1, text);

            // 情感分析
            let request = AIMLRequest::TextAnalysis {
                text: text.clone(),
                task: TextTask::SentimentAnalysis,
            };

            let response = self.service.process_request(request).await?;
            if let AIMLResult::TextAnalysis { sentiment, .. } = response.result {
                if let Some(sentiment) = sentiment {
                    println!(
                        "  💭 情感分析: {} (置信度: {:.2})",
                        sentiment.sentiment, sentiment.score
                    );
                }
            }

            // 关键词提取
            let request = AIMLRequest::TextAnalysis {
                text: text.clone(),
                task: TextTask::KeywordExtraction,
            };

            let response = self.service.process_request(request).await?;
            if let AIMLResult::TextAnalysis { keywords, .. } = response.result {
                if let Some(keywords) = keywords {
                    println!("  🔑 关键词: {:?}", keywords);
                }
            }

            // 文本摘要
            let request = AIMLRequest::TextAnalysis {
                text: text.clone(),
                task: TextTask::Summarization,
            };

            let response = self.service.process_request(request).await?;
            if let AIMLResult::TextAnalysis { summary, .. } = response.result {
                if let Some(summary) = summary {
                    println!("  📄 摘要: {}", summary);
                }
            }

            println!("  ⏱️  处理时间: {}ms", response.processing_time_ms);
        }

        Ok(())
    }

    /// 演示文本分析功能（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_text_analysis(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过文本分析演示");
        Ok(())
    }

    /// 演示图像分析功能
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_image_analysis(&self) -> Result<()> {
        println!("\n🖼️  演示图像分析功能:");
        println!("================================");

        // 模拟图像数据
        let image_data = vec![0u8; 1024]; // 模拟 1KB 图像数据

        let image_tasks = vec![
            ("图像分类", ImageTask::Classification),
            ("目标检测", ImageTask::ObjectDetection),
            ("人脸检测", ImageTask::FaceDetection),
            ("文本提取", ImageTask::TextExtraction),
            ("场景分析", ImageTask::SceneAnalysis),
        ];

        for (task_name, task) in image_tasks {
            println!("\n{}:", task_name);

            let request = AIMLRequest::ImageAnalysis {
                image_data: image_data.clone(),
                task,
            };

            let response = self.service.process_request(request).await?;

            match response.result {
                AIMLResult::ImageAnalysis {
                    classification,
                    objects,
                    faces,
                    extracted_text,
                    scene,
                    ..
                } => {
                    if let Some(classification) = classification {
                        println!("  分类结果: {:?}", classification);
                    }
                    if let Some(objects) = objects {
                        println!("  检测到的对象: {:?}", objects);
                    }
                    if let Some(faces) = faces {
                        println!("  检测到的人脸: {:?}", faces);
                    }
                    if let Some(text) = extracted_text {
                        println!("  提取的文本: {}", text);
                    }
                    if let Some(scene) = scene {
                        println!("  场景分析: {}", scene);
                    }
                }
                _ => println!("  未支持的结果类型"),
            }

            println!("  ⏱️  处理时间: {}ms", response.processing_time_ms);
        }

        Ok(())
    }

    /// 演示图像分析功能（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_image_analysis(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过图像分析演示");
        Ok(())
    }

    /// 演示推荐系统功能
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_recommendation_system(&self) -> Result<()> {
        println!("\n🎯 演示推荐系统功能:");
        println!("================================");

        let test_users = vec!["user1", "user2", "user3"];
        let item_types = vec!["movie", "book", "product", "music"];

        for user_id in test_users {
            println!("\n用户 {} 的推荐:", user_id);

            for item_type in &item_types {
                let request = AIMLRequest::Recommendation {
                    user_id: user_id.to_string(),
                    item_type: item_type.to_string(),
                    limit: 5,
                };

                let response = self.service.process_request(request).await?;

                if let AIMLResult::Recommendation { items, reasoning } = response.result {
                    println!("  {} 推荐:", item_type);
                    for (i, item) in items.iter().enumerate() {
                        println!(
                            "    {}. {} (分数: {:.2}) - {}",
                            i + 1,
                            item.item_id,
                            item.score,
                            item.reason
                        );
                    }
                    println!("  推荐理由: {}", reasoning);
                }

                println!("  ⏱️  处理时间: {}ms", response.processing_time_ms);
            }
        }

        Ok(())
    }

    /// 演示推荐系统功能（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_recommendation_system(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过推荐系统演示");
        Ok(())
    }

    /// 演示异常检测功能
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_anomaly_detection(&self) -> Result<()> {
        println!("\n🚨 演示异常检测功能:");
        println!("================================");

        let test_datasets = vec![
            ("正常数据", vec![1.0, 2.0, 3.0, 2.5, 2.8, 3.2, 2.9, 3.1]),
            ("异常数据", vec![1.0, 2.0, 3.0, 2.5, 2.8, 10.0, 2.9, 3.1]), // 包含异常值
            ("系统指标", vec![0.5, 0.6, 0.7, 0.8, 0.9, 0.85, 0.75, 0.65]),
            (
                "网络延迟",
                vec![10.0, 12.0, 15.0, 11.0, 13.0, 100.0, 14.0, 12.5],
            ), // 包含网络异常
        ];

        for (dataset_name, data) in test_datasets {
            println!("\n{}: {:?}", dataset_name, data);

            let request = AIMLRequest::AnomalyDetection {
                data: data.clone(),
                threshold: 2.0, // 标准差阈值
            };

            let response = self.service.process_request(request).await?;

            if let AIMLResult::AnomalyDetection {
                is_anomaly,
                anomaly_score,
                explanation,
            } = response.result
            {
                let status = if is_anomaly {
                    "🚨 异常"
                } else {
                    "✅ 正常"
                };
                println!("  {} 异常分数: {:.3}", status, anomaly_score);
                println!("  解释: {}", explanation);
            }

            println!("  ⏱️  处理时间: {}ms", response.processing_time_ms);
        }

        Ok(())
    }

    /// 演示异常检测功能（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_anomaly_detection(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过异常检测演示");
        Ok(())
    }

    /// 演示批量处理
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_batch_processing(&self) -> Result<()> {
        println!("\n📦 演示批量处理:");
        println!("================================");

        let batch_size = 10;
        let requests: Vec<AIMLRequest> = (1..=batch_size)
            .map(|i| AIMLRequest::TextAnalysis {
                text: format!("这是第 {} 个测试文本，用于演示批量处理功能。", i),
                task: TextTask::SentimentAnalysis,
            })
            .collect();

        println!("处理 {} 个请求...", batch_size);

        let start_time = std::time::Instant::now();
        let handles: Vec<_> = requests
            .into_iter()
            .map(|request| {
                let service = &self.service;
                tokio::spawn(async move { service.process_request(request).await })
            })
            .collect();

        let mut success_count = 0;
        let mut total_time = 0;

        for handle in handles {
            match handle.await {
                Ok(Ok(response)) => {
                    success_count += 1;
                    total_time += response.processing_time_ms;
                }
                Ok(Err(e)) => {
                    println!("请求处理失败: {}", e);
                }
                Err(e) => {
                    println!("任务执行失败: {}", e);
                }
            }
        }

        let total_time_elapsed = start_time.elapsed().as_millis() as u64;
        let average_time = if success_count > 0 {
            total_time / success_count
        } else {
            0
        };

        println!("批量处理完成:");
        println!("  - 成功请求: {}/{}", success_count, batch_size);
        println!("  - 总耗时: {}ms", total_time_elapsed);
        println!("  - 平均处理时间: {}ms", average_time);
        println!(
            "  - 吞吐量: {:.2} req/s",
            (success_count as f64 * 1000.0) / total_time_elapsed as f64
        );

        Ok(())
    }

    /// 演示批量处理（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_batch_processing(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过批量处理演示");
        Ok(())
    }

    /// 演示服务指标
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_service_metrics(&self) -> Result<()> {
        println!("\n📊 演示服务指标:");
        println!("================================");

        let metrics = self.service.get_metrics().await;

        println!("AI/ML 服务指标:");
        println!("  - 总请求数: {}", metrics.total_requests);
        println!("  - 成功请求数: {}", metrics.successful_requests);
        println!("  - 失败请求数: {}", metrics.failed_requests);
        println!(
            "  - 平均响应时间: {:.2}ms",
            metrics.average_response_time_ms
        );
        println!("  - 模型加载次数: {}", metrics.model_load_count);
        println!("  - 缓存命中率: {:.2}%", metrics.cache_hit_rate * 100.0);

        if metrics.total_requests > 0 {
            let success_rate =
                (metrics.successful_requests as f64 / metrics.total_requests as f64) * 100.0;
            println!("  - 成功率: {:.2}%", success_rate);
        }

        Ok(())
    }

    /// 演示服务指标（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_service_metrics(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过服务指标演示");
        Ok(())
    }

    /// 演示性能基准测试
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_performance_benchmark(&self) -> Result<()> {
        println!("\n⚡ 演示性能基准测试:");
        println!("================================");

        let iterations = 100;
        let mut total_time = 0;
        let mut success_count = 0;

        println!("执行 {} 次情感分析请求...", iterations);

        for i in 1..=iterations {
            let request = AIMLRequest::TextAnalysis {
                text: format!("基准测试文本 #{}", i),
                task: TextTask::SentimentAnalysis,
            };

            let start = std::time::Instant::now();
            match self.service.process_request(request).await {
                Ok(response) => {
                    let duration = start.elapsed().as_millis() as u64;
                    total_time += duration;
                    success_count += 1;

                    if i % 20 == 0 {
                        println!("  已完成 {}/{} 请求", i, iterations);
                    }
                }
                Err(e) => {
                    println!("  请求 {} 失败: {}", i, e);
                }
            }
        }

        let average_time = if success_count > 0 {
            total_time / success_count
        } else {
            0
        };
        let throughput = if total_time > 0 {
            (success_count as f64 * 1000.0) / total_time as f64
        } else {
            0.0
        };

        println!("\n基准测试结果:");
        println!("  - 总请求数: {}", iterations);
        println!("  - 成功请求数: {}", success_count);
        println!(
            "  - 成功率: {:.2}%",
            (success_count as f64 / iterations as f64) * 100.0
        );
        println!("  - 平均响应时间: {}ms", average_time);
        println!("  - 吞吐量: {:.2} req/s", throughput);

        Ok(())
    }

    /// 演示性能基准测试（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_performance_benchmark(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过性能基准测试演示");
        Ok(())
    }

    /// 演示配置管理
    #[cfg(feature = "with-ai-ml")]
    pub async fn demo_configuration_management(&self) -> Result<()> {
        println!("\n⚙️  演示配置管理:");
        println!("================================");

        let current_metrics = self.service.get_metrics().await;
        println!("当前配置:");
        println!("  - 模型缓存大小: {}", self.service.config.model_cache_size);
        println!(
            "  - 推理超时时间: {}ms",
            self.service.config.inference_timeout_ms
        );
        println!("  - 批处理大小: {}", self.service.config.batch_size);
        println!("  - GPU 加速: {}", self.service.config.enable_gpu);
        println!(
            "  - 模型更新间隔: {}s",
            self.service.config.model_update_interval
        );

        println!("\n性能优化建议:");
        if current_metrics.average_response_time_ms > 1000.0 {
            println!("  - 平均响应时间较高，建议启用 GPU 加速");
        }
        if current_metrics.cache_hit_rate < 0.8 {
            println!("  - 缓存命中率较低，建议增加缓存大小");
        }
        if current_metrics.total_requests > 1000 {
            println!("  - 请求量较大，建议增加批处理大小");
        }

        Ok(())
    }

    /// 演示配置管理（非 AI/ML 特性版本）
    #[cfg(not(feature = "with-ai-ml"))]
    pub async fn demo_configuration_management(&self) -> Result<()> {
        println!("⚠️  AI/ML 功能未启用，跳过配置管理演示");
        Ok(())
    }
}

/// 主函数演示高级 AI/ML 功能
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🤖 高级 AI/ML 功能演示");
    println!("================================");

    // 检查是否启用了 AI/ML 功能
    #[cfg(not(feature = "with-ai-ml"))]
    {
        println!("⚠️  AI/ML 功能未启用");
        println!("请使用以下命令启用:");
        println!("  cargo run --example advanced_ai_ml_demo --features with-ai-ml");
        return Ok(());
    }

    // 创建 AI/ML 演示管理器
    let demo_manager = AIMLDemoManager::new();

    // 初始化 AI/ML 服务
    #[cfg(feature = "with-ai-ml")]
    demo_manager.initialize().await?;

    // 演示文本分析功能
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_text_analysis().await?;

    // 演示图像分析功能
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_image_analysis().await?;

    // 演示推荐系统功能
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_recommendation_system().await?;

    // 演示异常检测功能
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_anomaly_detection().await?;

    // 演示批量处理
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_batch_processing().await?;

    // 演示性能基准测试
    #[cfg(feature = "with-ai-ml")]
    demo_manager.demo_performance_benchmark().await?;

    // 演示服务指标
    demo_manager.demo_service_metrics().await?;

    // 演示配置管理
    demo_manager.demo_configuration_management().await?;

    println!("\n✅ 高级 AI/ML 功能演示完成！");
    println!();
    println!("🎯 主要特性:");
    println!("- 多模态 AI 服务（文本、图像、语音）");
    println!("- 智能推荐系统");
    println!("- 异常检测和监控");
    println!("- 模型管理和版本控制");
    println!("- 实时推理服务");
    println!("- 批量处理和性能优化");
    println!("- 完整的指标监控");
    println!("- 灵活的配置管理");
    println!();
    println!("📚 支持的 AI 框架:");
    println!("- Candle: Rust 原生深度学习框架");
    println!("- ONNX Runtime: 跨平台推理引擎");
    println!("- PyTorch: 通过 tch 绑定");
    println!("- Tokenizers: 文本处理工具");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[cfg(feature = "with-ai-ml")]
    async fn test_ai_ml_demo_manager() {
        let demo_manager = AIMLDemoManager::new();
        let metrics = demo_manager.service.get_metrics().await;
        assert_eq!(metrics.total_requests, 0);
    }

    #[tokio::test]
    #[cfg(not(feature = "with-ai-ml"))]
    async fn test_ai_ml_demo_manager_no_feature() {
        let demo_manager = AIMLDemoManager::new();
        // 对于非 AI/ML 特性版本，只测试结构体创建
        assert!(true); // 简单的断言，确保结构体可以创建
    }

    #[cfg(feature = "with-ai-ml")]
    #[tokio::test]
    async fn test_text_analysis() {
        let demo_manager = AIMLDemoManager::new();
        demo_manager.initialize().await.unwrap();

        let request = AIMLRequest::TextAnalysis {
            text: "这是一个测试文本".to_string(),
            task: TextTask::SentimentAnalysis,
        };

        let response = demo_manager.service.process_request(request).await.unwrap();
        assert!(response.confidence > 0.0);
    }
}
