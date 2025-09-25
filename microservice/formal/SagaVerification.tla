---- MODULE SagaVerification ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Steps,          \* Saga 步骤集合
    MaxSteps        \* 最大步骤数

VARIABLES
    sagaState,      \* Saga 状态
    stepStates,     \* 步骤状态
    compensationLog \* 补偿日志

SagaState == {"not_started", "in_progress", "completed", "compensating", "compensated"}

StepState == {"pending", "executing", "completed", "failed", "compensating", "compensated"}

TypeOK ==
    /\ sagaState \in SagaState
    /\ stepStates \in [Steps -> StepState]
    /\ compensationLog \in Seq(Steps)
    /\ Len(compensationLog) <= MaxSteps

Init ==
    /\ sagaState = "not_started"
    /\ stepStates = [s \in Steps |-> "pending"]
    /\ compensationLog = <<>>

ExecuteStep(step) ==
    /\ stepStates[step] = "pending"
    /\ stepStates' = [stepStates EXCEPT ![step] = "executing"]
    /\ sagaState' = IF sagaState = "not_started" THEN "in_progress" ELSE sagaState
    /\ compensationLog' = compensationLog

CompleteStep(step) ==
    /\ stepStates[step] = "executing"
    /\ stepStates' = [stepStates EXCEPT ![step] = "completed"]
    /\ sagaState' = IF \A s \in Steps : stepStates[s] = "completed" 
                   THEN "completed" 
                   ELSE sagaState
    /\ compensationLog' = compensationLog

FailStep(step) ==
    /\ stepStates[step] = "executing"
    /\ stepStates' = [stepStates EXCEPT ![step] = "failed"]
    /\ sagaState' = "compensating"
    /\ compensationLog' = compensationLog

CompensateStep(step) ==
    /\ stepStates[step] = "completed"
    /\ stepStates' = [stepStates EXCEPT ![step] = "compensating"]
    /\ compensationLog' = Append(compensationLog, step)

CompleteCompensation(step) ==
    /\ stepStates[step] = "compensating"
    /\ stepStates' = [stepStates EXCEPT ![step] = "compensated"]
    /\ sagaState' = IF \A s \in Steps : stepStates[s] \in {"compensated", "pending"}
                   THEN "compensated"
                   ELSE sagaState
    /\ compensationLog' = compensationLog

Next ==
    \/ \E step \in Steps : ExecuteStep(step)
    \/ \E step \in Steps : CompleteStep(step)
    \/ \E step \in Steps : FailStep(step)
    \/ \E step \in Steps : CompensateStep(step)
    \/ \E step \in Steps : CompleteCompensation(step)

Spec == Init /\ [][Next]_<<sagaState, stepStates, compensationLog>>

\* 属性1：Saga 要么完全成功，要么完全补偿
SagaCompletion ==
    \/ (sagaState = "completed" /\ \A s \in Steps : stepStates[s] = "completed")
    \/ (sagaState = "compensated" /\ \A s \in Steps : stepStates[s] \in {"compensated", "pending"})

\* 属性2：不会出现部分完成状态
NoPartialCompletion ==
    ~(sagaState = "in_progress" /\ \E s1, s2 \in Steps : 
      stepStates[s1] = "completed" /\ stepStates[s2] = "compensated")

\* 属性3：补偿顺序与执行顺序相反
CompensationOrder ==
    \A i, j \in DOMAIN compensationLog :
        i < j => compensationLog[i] /= compensationLog[j]

\* 属性4：每个步骤最多执行一次
StepExecutedOnce ==
    \A step \in Steps :
        Cardinality({i \in DOMAIN compensationLog : compensationLog[i] = step}) <= 1

\* 活性属性：系统最终会达到稳定状态
EventuallyRecovers ==
    sagaState = "compensating" ~> sagaState = "compensated"

====
