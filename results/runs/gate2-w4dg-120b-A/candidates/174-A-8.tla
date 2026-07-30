---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

MessageType == [kind: {"query", "reply", "term"}, src: Node, dst: Node, col: 1..2 \cup {NoColor}]

VARIABLES
  nodeColor,
  msgs,
  pc,
  sample,
  iters

vars == <<nodeColor, msgs, pc, sample, iters>>

LoopProc(n) == CHOOSE lp \in SlushLoopProcess : HostMapping[lp] = n
QueryProc(n) == CHOOSE qp \in SlushQueryProcess : HostMapping[qp] = n

TypeOK ==
  /\ nodeColor \in [Node -> (1..2) \cup {NoColor}]
  /\ msgs \subseteq MessageType
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "querying", "tallying", "done"} \cup {"listening"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iters = [lp \in SlushLoopProcess |-> 0]

\* Client assigns a random color to an uncolored node.
ClientAssignsColor ==
  /\ \E n \in Node, col \in 1..2 :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = col]
  /\ UNCHANGED <<msgs, pc, sample, iters>>

RequireColor(n) ==
  /\ pc[LoopProc(n)] = "idle"
  /\ nodeColor[n] # NoColor
  /\ pc' = [pc EXCEPT ![LoopProc(n)] = "listening"]
  /\ UNCHANGED <<nodeColor, msgs, sample, iters>>

\* Loop process picks a random sample of peers and emits a query.
QuerySampleSet(lp) ==
  /\ pc[lp] = "listening"
  /\ nodeColor[HostMapping[lp]] # NoColor
  /\ \E s \in SUBSET (Node \ {HostMapping[lp]}) : Cardinality(s) = SampleSetSize
       /\ sample' = [sample EXCEPT ![lp] = s]
       /\ msgs' = msgs \cup { [kind |-> "query", src |-> HostMapping[lp], dst |-> n, col |-> nodeColor[HostMapping[lp]]] : n \in s }
  /\ pc' = [pc EXCEPT ![lp] = "tallying"]
  /\ UNCHANGED <<nodeColor, iters>>

\* A query process adopts the query's color if it is uncolored, then replies.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ nodeColor' = [nodeColor EXCEPT ![m.dst] = IF nodeColor[m.dst] = NoColor THEN m.col ELSE nodeColor[m.dst]]
       /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> nodeColor[m.dst]]}
  /\ UNCHANGED <<pc, sample, iters>>

\* Loop process waits for all replies, then flips if a color reaches the threshold.
TallyReplies(lp) ==
  /\ pc[lp] = "tallying"
  /\ Cardinality({m \in msgs : m.kind = "reply" /\ m.dst = HostMapping[lp]}) = SampleSetSize
  /\ LET yes == Cardinality({m \in msgs : m.kind = "reply" /\ m.dst = HostMapping[lp] /\ m.col = 1})
         no == Cardinality({m \in msgs : m.kind = "reply" /\ m.dst = HostMapping[lp] /\ m.col = 2})
     IN
       /\ IF yes >= PickFlipThreshold THEN nodeColor' = [nodeColor EXCEPT ![HostMapping[lp]] = 1]
          ELSE IF no >= PickFlipThreshold THEN nodeColor' = [nodeColor EXCEPT ![HostMapping[lp]] = 2]
          ELSE nodeColor'
       /\ msgs' = {m \in msgs : m.kind # "reply"}
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ iters' = [iters EXCEPT ![lp] = IF iters[lp] < SlushIterationCount THEN iters[lp] + 1 ELSE iters[lp]]
  /\ pc' = [pc EXCEPT ![lp] = IF iters[lp] < SlushIterationCount THEN "listening" ELSE "done"]

\* After all iterations, the loop process broadcasts termination.
LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "done"
       /\ msgs' = msgs \cup {[kind |-> "term", src |-> HostMapping[lp], dst |-> HostMapping[lp], col |-> NoColor]}
       /\ pc' = [pc EXCEPT ![lp] = "idle"]
  /\ UNCHANGED <<nodeColor, sample, iters>>

\* Query processes exit once every loop process has terminated.
QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : pc[lp] = "idle"
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] # "done"
       /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<nodeColor, msgs, sample, iters>>

Next ==
  \/ ClientAssignsColor
  \/ \E n \in Node : RequireColor(n)
  \/ \E lp \in SlushLoopProcess : QuerySampleSet(lp)
  \/ RespondToQuery
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllProcessesTerminated ==
  /\ \A n \in Node : nodeColor[n] # NoColor
  /\ \A lp \in SlushLoopProcess : pc[lp] = "idle"
  /\ \A qp \in SlushQueryProcess : pc[qp] = "done"

====