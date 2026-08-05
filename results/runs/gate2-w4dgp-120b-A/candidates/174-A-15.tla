---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME NoColor \notin Node
ASSUME NoMessage \notin Node

Processes == SlushLoopProcess \cup SlushQueryProcess

Color == {NoColor} \cup Node

Message == {NoMessage} \cup [kind : {"q", "reply", "done"}, to : Processes, from : Processes, clr : Color]

VARIABLES color, msgs, pc, sample, iter

vars == <<color, msgs, pc, sample, iter>>

\* HostMapping links a SlushLoopProcess and its SlushQueryProcess to the
\* underlying node, so a message from a loop process to a query process
\* names the process explicitly even though both belong to one node.
ProcessNode(p) == CHOOSE n \in Node : \E lp, qp \in SlushLoopProcess \times SlushQueryProcess : <<lp, qp, n>> \in HostMapping /\ (p = lp \/ p = qp)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {NoMessage}
  /\ pc = [p \in Processes |-> IF p \in SlushLoopProcess THEN "waitingForColor" ELSE "replyLoop"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter = [p \in SlushLoopProcess |-> 0]

AssignColor(sm) ==
  /\ pc[SlushLoopProcess] = "waitingForColor"
  /\ color[sm] = NoColor
  /\ \E c \in Node :
       color' = [color EXCEPT ![sm] = c]
  /\ UNCHANGED <<msgs, pc, sample, iter>>

RequireColor(p) ==
  /\ pc[p] = "waitingForColor"
  /\ color[ProcessNode(p)] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

QuerySampleSet(p) ==
  /\ pc[p] = "idle"
  /\ iter[p] < SlushIterationCount
  /\ Cardinality(sample[p]) = 0
  /\ \E s \in (SlushQueryProcess \ {ProcessNode(p)}) :
       Cardinality(s) = SampleSetSize /\ sample' = [sample EXCEPT ![p] = s]
  /\ msgs' = { [kind |-> "q", to |-> qp, from |-> p, clr |-> color[ProcessNode(p)]] : qp \in sample' [p] }
  /\ UNCHANGED <<color, pc, iter>>

RespondQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "q"
       /\ LET qp == m.to IN
         /\ color[ProcessNode(qp)] = NoColor
         /\ color' = [color EXCEPT ![ProcessNode(qp)] = m.clr]
         /\ msgs' = {NoMessage} \cup { [kind |-> "reply", to |-> m.from, from |-> qp, clr |-> color[ProcessNode(qp)]] }
  /\ UNCHANGED <<pc, sample, iter>>

TallyReplies(p) ==
  /\ Cardinality(sample[p]) > 0
  /\ \A qp \in sample[p] : [kind |-> "reply", to |-> p, from |-> qp, clr |-> color[ProcessNode(qp)]] \in msgs
  /\ LET Num(c) == Cardinality({ qp \in sample[p] : color[ProcessNode(qp)] = c })
         NewColor == IF Num(NoColor) >= PickFlipThreshold THEN NoColor
                       ELSE IF Num(ProcessNode(p)) >= PickFlipThreshold THEN ProcessNode(p)
                       ELSE IF \E x \in Node \ {ProcessNode(p)} : Num(x) >= PickFlipThreshold THEN CHOOSE x \in Node \ {ProcessNode(p)} : Num(x) >= PickFlipThreshold
                       ELSE color[ProcessNode(p)]
     IN color' = [color EXCEPT ![ProcessNode(p)] = NewColor]
  /\ msgs' = msgs \ { m \in msgs : m.kind = "reply" /\ m.to = p }
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iter' = [iter EXCEPT ![p] = iter[p] + 1]
  /\ UNCHANGED <<pc>>

BroadcastTermination(p) ==
  /\ iter[p] >= SlushIterationCount
  /\ sample[p] = {}
  /\ pc[p] = "idle"
  /\ msgs' = msgs \cup { [kind |-> "done", to |-> p, from |-> p, clr |-> NoColor] }
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iter>>

ReplyLoopExit ==
  /\ pc[SlushQueryProcess] = "replyLoop"
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ pc' = [pc EXCEPT ![SlushQueryProcess] = "done"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
  \/ \E sm \in Node : AssignColor(sm)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ RespondQuery
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : BroadcastTermination(p)
  \/ ReplyLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RespondQuery)

TypeInvariant ==
  /\ color \in [Node -> Color]
  /\ msgs \subseteq Message
  /\ pc \in [Processes -> {"waitingForColor", "idle", "replyLoop", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iter \in [SlushLoopProcess -> 0..SlushIterationCount]

ProcessQuiesce == \A p \in Processes : (p \in SlushLoopProcess) ~> (pc[p] = "done")

====