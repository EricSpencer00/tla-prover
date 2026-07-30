---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* State: each node's color, the in-flight message set, a program counter
\* per process, each loop process's current sample set, and its iteration count.
VARIABLES color, msgs, pc, sampleSet, loopIters

vars == <<color, msgs, pc, sampleSet, loopIters>>

\* Each node is hosted by exactly one loop process and one query process.
HostedBy(n) == CHOOSE p \in SlushLoopProcess : <<n, p>> \in HostMapping
QueriedBy(n) == CHOOSE qp \in SlushQueryProcess : <<n, qp>> \in HostMapping

Message == [kind: {"query", "reply", "term"}, from: SlushLoopProcess \cup SlushQueryProcess, to: SlushLoopProcess \cup SlushQueryProcess, col: {NoColor} \cup {0, 1}]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "idle"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopIters = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor(n) ==
  /\ pc["client"] = "idle"
  /\ color[n] = NoColor
  /\ \E c \in {0, 1} : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "assigned"]
  /\ UNCHANGED <<msgs, sampleSet, loopIters>>

LoopRequireColor(lp) ==
  /\ pc[lp] = "idle"
  /\ color[HostedBy(lp)] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "ready"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIters>>

QuerySampleSet(lp) ==
  /\ pc[lp] = "ready"
  /\ loopIters[lp] < SlushIterationCount
  /\ \E peers \in SUBSET SlushQueryProcess :
       peers \ {QueriedBy(HostedBy(lp))}
         \subseteq SlushQueryProcess /\ Cardinality(peers) = SampleSetSize
       /\ msgs' = msgs \cup {[kind |-> "query", from |-> lp, to |-> q, col |-> color[HostedBy(lp)]]
                              : q \in peers}
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
  /\ pc' = [pc EXCEPT ![lp] = "tally"]
  /\ UNCHANGED <<color, loopIters>>

RespondToQuery(qp) ==
  /\ pc[qp] = "idle"
  /\ \E m \in msgs :
       /\ m.kind = "query" /\ m.to = qp
       /\ color' = [color EXCEPT ![QueriedBy(qp)] =
                       IF color[QueriedBy(qp)] = NoColor THEN m.col ELSE color[QueriedBy(qp)]]
       /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", from |-> qp, to |-> m.from, col |->
                       IF color[QueriedBy(qp)] = NoColor THEN m.col ELSE color[QueriedBy(qp)]]}
  /\ pc' = [pc EXCEPT ![qp] = "replied"]
  /\ UNCHANGED <<sampleSet, loopIters>>

TallyReplies(lp) ==
  /\ pc[lp] = "tally"
  /\ \A q \in sampleSet[lp] : \E m \in msgs : m.kind = "reply" /\ m.from = q /\ m.to = lp
  /\ LET replies == {m \in msgs : m.kind = "reply" /\ m.to = lp}
         counts(c) == Cardinality({m \in replies : m.col = c})
     IN /\ \E c \in {0, 1} : counts(c) >= PickFlipThreshold /\ color' = [color EXCEPT ![HostedBy(lp)] = c]
        /\ msgs' = msgs \ {m \in replies : TRUE}
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ loopIters' = [loopIters EXCEPT ![lp] = @ + 1]
  /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ UNCHANGED <<color>>

LoopTerminate(lp) ==
  /\ pc[lp] = "done"
  /\ loopIters[lp] = SlushIterationCount
  /\ msgs' = msgs \cup {[kind |-> "term", from |-> lp, to |-> NoMessage, col |-> NoColor]}
  /\ UNCHANGED <<color, sampleSet, loopIters, pc>>

QueryLoopExit(qp) ==
  /\ pc[qp] \in {"idle", "replied"}
  /\ \A lp \in SlushLoopProcess : [kind |-> "term", from |-> lp, to |-> NoMessage, col |-> NoColor] \in msgs
  /\ pc' = [pc EXCEPT ![qp] = "quit"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopIters>>

Next ==
  \/ \E n \in Node : ClientAssignColor(n)
  \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp) \/ QuerySampleSet(lp) \/ TallyReplies(lp) \/ LoopTerminate(lp)
  \/ \E qp \in SlushQueryProcess : RespondToQuery(qp) \/ QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup {0, 1}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "ready", "tally", "done", "quit", "assigned", "replied"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIters \in [SlushLoopProcess -> Nat]

Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : <>(pc[p] \in {"done", "quit"})
====