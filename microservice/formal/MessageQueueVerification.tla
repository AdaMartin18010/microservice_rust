---- MODULE MessageQueueVerification ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxMessages,     \* 最大消息数
    MaxRetries       \* 最大重试次数

VARIABLES
    queue,           \* 消息队列
    processing,      \* 正在处理的消息
    processed,       \* 已处理的消息
    failed,          \* 失败的消息
    retryCount       \* 重试计数

Message == [id: Nat, data: STRING, timestamp: Nat]

TypeOK ==
    /\ queue \in Seq(Message)
    /\ processing \in Seq(Message)
    /\ processed \in Seq(Message)
    /\ failed \in Seq(Message)
    /\ retryCount \in [Message -> 0..MaxRetries]
    /\ Len(queue) + Len(processing) + Len(processed) + Len(failed) <= MaxMessages

Init ==
    /\ queue = <<>>
    /\ processing = <<>>
    /\ processed = <<>>
    /\ failed = <<>>
    /\ retryCount = [m \in Message |-> 0]

DequeueMessage ==
    /\ queue /= <<>>
    /\ LET msg == Head(queue)
       IN /\ queue' = Tail(queue)
          /\ processing' = Append(processing, msg)
          /\ UNCHANGED <<processed, failed, retryCount>>

ProcessMessage ==
    /\ processing /= <<>>
    /\ LET msg == Head(processing)
       IN /\ processing' = Tail(processing)
          /\ processed' = Append(processed, msg)
          /\ UNCHANGED <<queue, failed, retryCount>>

FailMessage ==
    /\ processing /= <<>>
    /\ LET msg == Head(processing)
       IN /\ processing' = Tail(processing)
          /\ retryCount' = [retryCount EXCEPT ![msg] = @ + 1]
          /\ failed' = IF retryCount[msg] < MaxRetries
                       THEN Append(failed, msg)
                       ELSE failed
          /\ UNCHANGED <<queue, processed>>

RetryMessage ==
    /\ failed /= <<>>
    /\ LET msg == Head(failed)
       IN /\ failed' = Tail(failed)
          /\ queue' = Append(queue, msg)
          /\ UNCHANGED <<processing, processed, retryCount>>

Next ==
    \/ DequeueMessage
    \/ ProcessMessage
    \/ FailMessage
    \/ RetryMessage

Spec == Init /\ [][Next]_<<queue, processing, processed, failed, retryCount>>

\* 属性1：消息不会丢失
NoMessageLoss ==
    \A msg \in Message :
        msg \in queue \/ msg \in processing \/ msg \in processed \/ msg \in failed

\* 属性2：消息不会重复处理
NoDuplicateProcessing ==
    \A msg \in Message :
        Cardinality({i \in DOMAIN processed : processed[i] = msg}) <= 1

\* 属性3：失败消息最终会重试
FailedMessagesEventuallyRetry ==
    \A msg \in Message :
        msg \in failed ~> msg \in queue

\* 属性4：重试次数有上限
RetryCountBounded ==
    \A msg \in Message :
        retryCount[msg] <= MaxRetries

\* 属性5：处理中的消息数量有上限
ProcessingBounded ==
    Len(processing) <= MaxMessages

\* 属性6：队列长度有上限
QueueBounded ==
    Len(queue) <= MaxMessages

====
