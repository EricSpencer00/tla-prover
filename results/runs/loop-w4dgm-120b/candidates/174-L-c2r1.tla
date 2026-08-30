---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

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

\* HostMapping is a set of triples (node, loop process, query process)
LoopFor(n) == CHOOSE p \in SlushLoopProcess : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping
QueryFor(n) == CHOOSE q \in SlushQueryProcess : \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

Message == [kind: {"query", "reply", "term"}, lp: SlushLoopProcess, qp: SlushQueryProcess, col: NoColor \cup (1..2)]

VARIABLES assign, msgSet, pc, sample, iters

vars == <<assign, msgSet, pc, sample, iters>>

TypeOK ==
  /\ assign \in [Node -> (1..2) \cup {NoColor}]
  /\ msgSet \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waitingColor", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assign = [n \in Node |-> NoColor]
  /\ msgSet = {}
  /\ pc = [p \in SlushLoopProcess |-> "waitingColor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  \E n \in Node, col \in 1..2 :
    /\ assign[n] = NoColor
    /\ assign' = [assign EXCEPT ![n] = col]
    /\ UNCHANGED <<msgSet, pc, sample, iters>>

RequireColor(p) ==
  /\ pc[p] = "waitingColor"
  /\ assign[LoopFor(p)] \in 1..2
  /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<assign, msgSet, sample, iters>>

QuerySampleSet(p) ==
  /\ pc[p] = "sampling"
  /\ sample' = [sample EXCEPT ![p] = {q \in SlushQueryProcess : q # QueryFor(LoopFor(p))} \cap SampleSetSize]
  /\ msgSet' = msgSet \cup {[kind |-> "query", lp |-> p, qp |-> q, col |-> assign[LoopFor(p)]] : q \in sample[p]}
  /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<assign, iters>>

RespondToQuery(msg) ==
  /\ msg \in msgSet
  /\ msg.kind = "query"
  /\ assign' = [assign EXCEPT ![LoopFor(QueryFor(msg.qp))] =
                  IF assign[LoopFor(QueryFor(msg.qp))] = NoColor THEN msg.col ELSE assign[LoopFor(QueryFor(msg.qp))]]
  /\ msgSet' = (msgSet \ {msg}) \cup {[kind |-> "reply", lp |-> msg.lp, qp |-> msg.qp, col |-> assign[LoopFor(QueryFor(msg.qp))]]}
  /\ UNCHANGED <<pc, sample, iters>>

TallyReplies(p) ==
  /\ pc[p] = "tallying"
  /\ {msg \in msgSet : msg.kind = "reply" /\ msg.lp = p} = {msg \in Message : msg.kind = "reply" /\ msg.lp = p}
  /\ \E col \in 1..2 :
       /\ Cardinality({msg \in msgSet : msg.kind = "reply" /\ msg.lp = p /\ msg.col = col}) >= PickFlipThreshold
       /\ assign' = [assign EXCEPT ![LoopFor(p)] = col]
  /\ msgSet' = msgSet \ {msg \in msgSet : msg.kind = "reply" /\ msg.lp = p}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
  /\ pc' = IF iters[p] + 1 >= SlushIterationCount THEN "done" ELSE "sampling"

LoopTermination(p) ==
  /\ pc[p] = "tallying"
  /\ {msg \in msgSet : msg.kind = "reply" /\ msg.lp = p} = {msg \in Message : msg.kind = "reply" /\ msg.lp = p}
  /\ msgSet' = msgSet \ {msg \in msgSet : msg.kind = "reply" /\ msg.lp = p}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
  /\ pc' = IF iters[p] + 1 >= SlushIterationCount THEN "done" ELSE "sampling"
  /\ assign' = assign

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A q \in SlushQueryProcess : pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<assign, msgSet, sample, iters>>

Next ==
  \/ ClientAssignColor
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ \E msg \in msgSet : RespondToQuery(msg)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTermination(p)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ \A msg \in msgSet : WF_vars(RespondToQuery(msg))

TypeInvariant == TypeOK

Termination == \A x \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[x] = "done")

====