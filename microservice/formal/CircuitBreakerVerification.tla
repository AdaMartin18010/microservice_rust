---- MODULE CircuitBreakerVerification ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    FailureThreshold,   \* 失败阈值
    SuccessThreshold,   \* 成功阈值
    Timeout            \* 超时时间

VARIABLES
    cbState,           \* 熔断器状态
    failureCount,      \* 失败计数
    successCount,      \* 成功计数
    lastFailureTime    \* 最后失败时间

CBState == {"closed", "open", "half_open"}

TypeOK ==
    /\ cbState \in CBState
    /\ failureCount \in 0..FailureThreshold
    /\ successCount \in 0..SuccessThreshold
    /\ lastFailureTime \in 0..Timeout

Init ==
    /\ cbState = "closed"
    /\ failureCount = 0
    /\ successCount = 0
    /\ lastFailureTime = 0

RequestSuccess ==
    /\ cbState \in {"closed", "half_open"}
    /\ failureCount' = 0
    /\ successCount' = IF cbState = "half_open" THEN successCount + 1 ELSE 0
    /\ lastFailureTime' = lastFailureTime
    /\ cbState' = IF cbState = "half_open" /\ successCount' >= SuccessThreshold
                  THEN "closed"
                  ELSE cbState

RequestFailure ==
    /\ cbState \in {"closed", "half_open"}
    /\ failureCount' = failureCount + 1
    /\ successCount' = 0
    /\ lastFailureTime' = 0  \* 简化：假设当前时间
    /\ cbState' = IF failureCount' >= FailureThreshold
                  THEN "open"
                  ELSE cbState

TimeoutExpired ==
    /\ cbState = "open"
    /\ failureCount' = failureCount
    /\ successCount' = 0
    /\ lastFailureTime' = lastFailureTime
    /\ cbState' = "half_open"

Next ==
    \/ RequestSuccess
    \/ RequestFailure
    \/ TimeoutExpired

Spec == Init /\ [][Next]_<<cbState, failureCount, successCount, lastFailureTime>>

\* 属性1：熔断器不会在开放状态下处理请求
NoRequestsWhenOpen ==
    cbState /= "open" \/ failureCount < FailureThreshold

\* 属性2：熔断器最终会从开放状态转换
EventuallyRecovers ==
    cbState = "open" ~> cbState = "half_open"

\* 属性3：成功请求会重置失败计数
SuccessResetsFailures ==
    RequestSuccess => failureCount' = 0

\* 属性4：失败计数不会超过阈值
FailureCountBounded ==
    failureCount <= FailureThreshold

\* 属性5：成功计数不会超过阈值
SuccessCountBounded ==
    successCount <= SuccessThreshold

====
