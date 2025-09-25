# TLA+ 形式化验证 Makefile
# 使用 Apalache 进行模型检查

.PHONY: all clean check-saga check-circuit-breaker check-message-queue

# 默认目标
all: check-saga check-circuit-breaker check-message-queue

# 清理生成的文件
clean:
	rm -f *.tla.bak
	rm -f *.log
	rm -f *.json

# 检查 Saga 模式
check-saga:
	@echo "检查 Saga 模式模型..."
	docker run --rm -v $(PWD):/var/apalache \
		apalache/mc:latest check \
		--config=saga-config.json \
		SagaVerification.tla

# 检查熔断器模式
check-circuit-breaker:
	@echo "检查熔断器模式模型..."
	docker run --rm -v $(PWD):/var/apalache \
		apalache/mc:latest check \
		--config=circuit-breaker-config.json \
		CircuitBreakerVerification.tla

# 检查消息队列模式
check-message-queue:
	@echo "检查消息队列模式模型..."
	docker run --rm -v $(PWD):/var/apalache \
		apalache/mc:latest check \
		--config=message-queue-config.json \
		MessageQueueVerification.tla

# 运行所有检查
check-all:
	@echo "运行所有形式化验证..."
	$(MAKE) check-saga
	$(MAKE) check-circuit-breaker
	$(MAKE) check-message-queue

# 生成测试用例
generate-tests:
	@echo "生成测试用例..."
	docker run --rm -v $(PWD):/var/apalache \
		apalache/mc:latest testgen \
		--config=saga-config.json \
		SagaVerification.tla

# 验证特定属性
verify-property:
	@echo "验证特定属性..."
	docker run --rm -v $(PWD):/var/apalache \
		apalache/mc:latest check \
		--config=saga-config.json \
		--inv=SagaCompletion \
		SagaVerification.tla

# 帮助信息
help:
	@echo "可用的目标："
	@echo "  all                    - 运行所有检查"
	@echo "  check-saga            - 检查 Saga 模式"
	@echo "  check-circuit-breaker - 检查熔断器模式"
	@echo "  check-message-queue   - 检查消息队列模式"
	@echo "  check-all             - 运行所有检查"
	@echo "  generate-tests        - 生成测试用例"
	@echo "  verify-property       - 验证特定属性"
	@echo "  clean                 - 清理生成的文件"
	@echo "  help                  - 显示此帮助信息"
