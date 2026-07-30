---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* Colors: two protocol colors plus the uncolored marker.
Colors == {"c1", "c2", NoColor}

MessageTypes == {"slushMsgQuery", "slushMsgReply", "slushMsgTerminate"}

\* A loop process sends a query to a query process; the message body is
\* the color it is currently carrying, which a receiver may adopt if it
\* is still uncolored.
MessageBody == [from : SlushLoopProcess, to : SlushQueryProcess, clr : Colors]

VARIABLES nodeColor, messages, pc, sample, iters

vars == <<nodeColor, messages, pc, sample, iters>>

TypeOK ==
  /\ nodeColor \in [Node -> Colors]
  /\ messages \subseteq [type : MessageTypes, body : MessageBody]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"slushReqClient"} -> {"wait", "querying", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"slushReqClient"}) |-> "wait"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iters = [lp \in SlushLoopProcess |-> 0]

\* The client assigns a random initial color to an uncolored node.
ReqClientAssignColor ==
  /\ pc["slushReqClient"] = "wait"
  /\ \E n \in Node :
       /\ nodeColor[n] = NoColor
       /\ \E c \in {"c1", "c2"} : nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, iters>>

LoopRequireColor ==
  /\ pc["slushReqClient"] = "done"
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "wait"
       /\ \E n \in Node :
            /\ <<n, lp>> \in HostMapping
            /\ nodeColor[n] # NoColor
            /\ pc' = [pc EXCEPT ![lp] = "querying"]
       /\ UNCHANGED <<nodeColor, messages, sample, iters>>

\* The loop process samples a fixed-size set of peers and queries them.
LoopQuerySample ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ iters[lp] < SlushIterationCount
       /\ Cardinality(sample[lp]) < SampleSetSize
       /\ \E qp \in SlushQueryProcess :
            /\ qp \notin sample[lp]
            /\ pc[qp] = "tallying"
            /\ sample' = [sample EXCEPT ![lp] = @ \cup {qp}]
            /\ messages' = messages \cup {[type |-> "slushMsgQuery", body |-> [from |-> lp, to |-> qp, clr |-> (CHOOSE n \in Node : <<n, lp>> \in HostMapping /\ nodeColor[n])]}
       /\ UNCHANGED <<nodeColor, pc, iters>>

\* A query process replies with its own color (adopting the query if uncolored).
QueryRespond ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "tallying"
       /\ \E m \in messages :
            /\ m.type = "slushMsgQuery" /\ m.body.to = qp
            /\ \E n \in Node : <<n, qp>> \in HostMapping
                 /\ nodeColor' = [nodeColor EXCEPT ![n] = IF nodeColor[n] = NoColor THEN m.body.clr ELSE nodeColor[n]]
            /\ messages' = (messages \ {m}) \cup {[type |-> "slushMsgReply", body |-> [from |-> m.body.from, to |-> qp, clr |-> nodeColor'[(CHOOSE n \in Node : <<n, qp>> \in HostMapping)]]]}
       /\ UNCHANGED <<pc, sample, iters>>

\* The loop process flips its node once the sample replies reach the flip
\* threshold (or it has exhausted its iterations and will terminate).
LoopTally ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ Cardinality(sample[lp]) = SampleSetSize
       /\ \A qp \in sample[lp] : \E m \in messages : m.type = "slushMsgReply" /\ m.body.from = lp /\ m.body.to = qp
       /\ \E c \in {"c1", "c2"} :
            /\ Cardinality({qp \in sample[lp] : \E m \in messages : m.type = "slushMsgReply" /\ m.body.from = lp /\ m.body.to = qp /\ m.body.clr = c}) >= PickFlipThreshold
            /\ nodeColor' = [nodeColor EXCEPT ![CHOOSE n \in Node : <<n, lp>> \in HostMapping] = c]
       /\ messages' = {m \in messages : m.type # "slushMsgReply" \/ m.body.from # lp}
       /\ sample' = [sample EXCEPT ![lp] = {}]
       /\ iters' = [iters EXCEPT ![lp] = @ + 1]
       /\ pc' = IF iters[lp] + 1 = SlushIterationCount
                 THEN [pc EXCEPT ![lp] = "done"]
                 ELSE [pc EXCEPT ![lp] = "querying"]
       /\ UNCHANGED <<nodeColor, pc, sample, iters>>

LoopTerminate ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "done"
       /\ pc' = [pc EXCEPT ![lp] = "done"]
       /\ messages' = messages \cup {[type |-> "slushMsgTerminate", body |-> [from |-> lp, to |-> lp, clr |-> NoColor]]}
       /\ UNCHANGED <<nodeColor, sample, iters>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "tallying"
       /\ \A lp \in SlushLoopProcess : [type |-> "slushMsgTerminate", body |-> [from |-> lp, to |-> lp, clr |-> NoColor]] \in messages
       /\ pc' = [pc EXCEPT ![qp] = "done"]
       /\ UNCHANGED <<nodeColor, messages, sample, iters>>

Next ==
  \/ ReqClientAssignColor
  \/ LoopRequireColor
  \/ LoopQuerySample
  \/ QueryRespond
  \/ LoopTally
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"slushReqClient"} : <>(pc[p] = "done")

====