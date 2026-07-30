---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A Slush node is either uncolored or takes one of two colors; this is the
\* shared assignment the loop processes converge to (or fail to).
Color == {NoColor} \cup {0, 1}

MessageType == [kind: {"query", "reply", "term", "assign"},
                 from: SlushLoopProcess \cup SlushQueryProcess \cup {"client"},
                 to: SlushLoopProcess \cup SlushQueryProcess \cup {"client"},
                 col: Color]

VARIABLES color, msg, pc, sampleSet, iters

vars == <<color, msg, pc, sampleSet, iters>>

TypeOK ==
  /\ color \in [Node -> Color]
  /\ msg \subseteq MessageType
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waitColor", "query", "tally", "done", "replyLoop", "exitReply"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msg = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> IF p \in SlushLoopProcess THEN "waitColor" ELSE IF p = "client" THEN "assign" ELSE "replyLoop"]
  /\ sampleSet = [k \in SlushLoopProcess |-> {}]
  /\ iters = [k \in SlushLoopProcess |-> 0]

\* The client assigns initial colors to nodes; no loop iteration is allowed
\* before every node is colored, which is what makes this well-defined.
ClientAssign ==
  /\ pc["client"] = "assign"
  /\ \E n \in Node, c \in {0, 1}:
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
       /\ msg' = msg \cup {[kind |-> "assign", from |-> "client", to |-> "client", col |-> c]}
  /\ UNCHANGED <<pc, sampleSet, iters>>

RequireColor ==
  /\ \E k \in SlushLoopProcess:
       /\ pc[k] = "waitColor"
       /\ (\E pr \in HostMapping : pr[1] = k /\ color[pr[2]] # NoColor)
       /\ pc' = [pc EXCEPT ![k] = "query"]
  /\ UNCHANGED <<color, msg, sampleSet, iters>>

QuerySampleSet ==
  /\ \E k \in SlushLoopProcess:
       /\ pc[k] = "query"
       /\ iters[k] < SlushIterationCount
       /\ \E ks \subseteq SlushQueryProcess:
            /\ ks # {}
            /\ Cardinality(ks) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![k] = ks]
  /\ UNCHANGED <<color, msg, pc, iters>>

RespondToQuery ==
  /\ \E qp \in SlushQueryProcess:
       /\ \E m \in msg :
            /\ m.kind = "query" /\ m.to = qp
            /\ \E pr \in HostMapping : pr[2] = qp
                 /\ LET n == pr[3] IN
                      /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.col] ELSE color
                      /\ msg' = (msg \ {m}) \cup {[kind |-> "reply", from |-> qp, to |-> m.from, col |-> IF color[n] = NoColor THEN m.col ELSE color[n]]}
  /\ UNCHANGED <<pc, sampleSet, iters>>

TallyReplies ==
  /\ \E k \in SlushLoopProcess:
       /\ pc[k] = "query"
       /\ \E rs \in SUBSET msg :
            /\ rs = {m \in msg : m.kind = "reply" /\ m.to = k}
            /\ rs # {}
            /\ \A qp \in sampleSet[k] : \E m \in rs : m.from = qp
            /\ Cardinality({m \in rs : m.col = 0}) >= PickFlipThreshold
               \/ Cardinality({m \in rs : m.col = 1}) >= PickFlipThreshold
            /\ \E pr \in HostMapping : pr[1] = k
                 /\ color' = [color EXCEPT ![pr[2]] =
                                IF Cardinality({m \in rs : m.col = 0}) >= PickFlipThreshold
                                  THEN 0
                                  ELSE IF Cardinality({m \in rs : m.col = 1}) >= PickFlipThreshold
                                    THEN 1 ELSE color[pr[2]]]
            /\ sampleSet' = [sampleSet EXCEPT ![k] = {}]
            /\ iters' = [iters EXCEPT ![k] = iters[k] + 1]
            /\ pc' = [pc EXCEPT ![k] = "tally"]
            /\ msg' = msg \ rs
  /\ UNCHANGED <<color, sampleSet, iters>>

LoopTerminate ==
  /\ \E k \in SlushLoopProcess:
       /\ pc[k] = "tally"
       /\ iters[k] = SlushIterationCount
       /\ msg' = msg \cup {[kind |-> "term", from |-> k, to |-> k, col |-> NoColor]}
       /\ pc' = [pc EXCEPT ![k] = "done"]
  /\ UNCHANGED <<color, sampleSet, iters>>

ReplyLoopExit ==
  /\ \E qp \in SlushQueryProcess:
       /\ pc[qp] = "replyLoop"
       /\ \A k \in SlushLoopProcess : pc[k] = "done"
       /\ pc' = [pc EXCEPT ![qp] = "exitReply"]
  /\ UNCHANGED <<color, msg, sampleSet, iters>>

Next ==
  \/ ClientAssign \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTerminate \/ ReplyLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssign) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(ReplyLoopExit)

TypeInvariant == TypeOK

AllDone == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done"

Termination == <>(AllDone)

====