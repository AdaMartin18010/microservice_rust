//! 性能基准测试
//!
//! 使用 Criterion 进行微服务性能基准测试

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use microservice::rust_190_optimized::{
    FixedSizeBuffer, OptimizedMicroService, OptimizedService, Priority, ServiceRequest,
};
use std::hint::black_box;
use std::time::Duration;
use tokio::runtime::Runtime;

fn benchmark_request_processing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("request_processing");
    group.measurement_time(Duration::from_secs(10));
    group.sample_size(100);

    for concurrent_requests in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_requests", concurrent_requests),
            concurrent_requests,
            |b, &concurrent_requests| {
                b.iter(|| {
                    rt.block_on(async {
                        let service = OptimizedMicroService::new(
                            "benchmark-service".to_string(),
                            concurrent_requests,
                        );

                        let request = ServiceRequest {
                            id: "benchmark-request".to_string(),
                            data: black_box(b"test data".to_vec()),
                            priority: Priority::Normal,
                            timeout_ms: 1000,
                        };

                        service.process_request(request).await
                    })
                })
            },
        );
    }

    group.finish();
}

fn benchmark_buffer_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("buffer_operations");

    for buffer_size in [64, 256, 1024, 4096].iter() {
        group.bench_with_input(
            BenchmarkId::new("buffer_size", buffer_size),
            buffer_size,
            |b, &buffer_size| {
                b.iter(|| match buffer_size {
                    64 => {
                        let mut buffer = FixedSizeBuffer::<64>::new();
                        for i in 0..64 {
                            buffer.push(black_box(i as u8)).unwrap();
                        }
                        let slice = buffer.as_slice();
                        black_box(slice);
                        slice.len()
                    }
                    256 => {
                        let mut buffer = FixedSizeBuffer::<256>::new();
                        for i in 0..256 {
                            buffer.push(black_box(i as u8)).unwrap();
                        }
                        let slice = buffer.as_slice();
                        black_box(slice);
                        slice.len()
                    }
                    1024 => {
                        let mut buffer = FixedSizeBuffer::<1024>::new();
                        for i in 0..1024 {
                            buffer.push(black_box(i as u8)).unwrap();
                        }
                        let slice = buffer.as_slice();
                        black_box(slice);
                        slice.len()
                    }
                    4096 => {
                        let mut buffer = FixedSizeBuffer::<4096>::new();
                        for i in 0..4096 {
                            buffer.push(black_box(i as u8)).unwrap();
                        }
                        let slice = buffer.as_slice();
                        black_box(slice);
                        slice.len()
                    }
                    _ => panic!("Unsupported buffer size"),
                })
            },
        );
    }

    group.finish();
}

fn benchmark_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("serialization");

    let request = ServiceRequest {
        id: "test-request".to_string(),
        data: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        priority: Priority::High,
        timeout_ms: 5000,
    };

    group.bench_function("serialize_request", |b| {
        b.iter(|| black_box(serde_json::to_string(&request).unwrap()))
    });

    group.bench_function("deserialize_request", |b| {
        let json = serde_json::to_string(&request).unwrap();
        b.iter(|| black_box(serde_json::from_str::<ServiceRequest>(&json).unwrap()))
    });

    group.finish();
}

fn benchmark_concurrent_processing(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("concurrent_processing");
    group.measurement_time(Duration::from_secs(15));

    for num_tasks in [1, 10, 50, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("num_tasks", num_tasks),
            num_tasks,
            |b, &num_tasks| {
                b.iter(|| {
                    rt.block_on(async {
                        let service =
                            OptimizedMicroService::new("concurrent-service".to_string(), num_tasks);

                        let tasks: Vec<_> = (0..num_tasks)
                            .map(|i| {
                                let service = &service;
                                async move {
                                    let request = ServiceRequest {
                                        id: format!("task-{}", i),
                                        data: black_box(b"concurrent test data".to_vec()),
                                        priority: Priority::Normal,
                                        timeout_ms: 1000,
                                    };

                                    service.process_request(request).await
                                }
                            })
                            .collect();

                        let results = futures::future::join_all(tasks).await;
                        black_box(results)
                    })
                })
            },
        );
    }

    group.finish();
}

fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");

    group.bench_function("buffer_allocation", |b| {
        b.iter(|| {
            let buffer = FixedSizeBuffer::<1024>::new();
            black_box(buffer)
        })
    });

    group.bench_function("service_creation", |b| {
        b.iter(|| {
            let service = OptimizedMicroService::new("memory-test".to_string(), 100);
            black_box(service)
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_request_processing,
    benchmark_buffer_operations,
    benchmark_serialization,
    benchmark_concurrent_processing,
    benchmark_memory_usage
);

criterion_main!(benches);
