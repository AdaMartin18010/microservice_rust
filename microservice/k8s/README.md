# K8s 最小模板入口

本目录提供文档中引用的最小化 Kubernetes 清单，便于快速验证。

## 清单文件

- `ingress-traefik.yaml` - HTTP 服务路由（参考 14.1）
- `deploy-grpc-service.yaml` - gRPC 服务部署（参考 14.2）
- `traefik-tcp-route.yaml` - gRPC TCP 路由（参考 14.2）
- `otel-collector.yaml` - 可观测性收集器（参考 8.1）
- `istio/canary.yaml` - 金丝雀发布（参考 14.5）

## 快速部署

```bash
# 创建命名空间
kubectl create namespace observability

# 部署观测栈
kubectl apply -f otel-collector.yaml

# 部署 gRPC 服务
kubectl apply -f deploy-grpc-service.yaml
kubectl apply -f traefik-tcp-route.yaml

# 部署 HTTP 服务路由
kubectl apply -f ingress-traefik.yaml

# Istio 金丝雀（需要先安装 Istio）
kubectl apply -f istio/canary.yaml
```

## 配置说明

- 镜像地址需要替换为实际仓库
- TLS 证书需要预先创建 Secret
- 根据环境调整资源限制和副本数
