---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* Each loop process is hosted by exactly one node, as is each query process.
\* The host mapping is a set of triples (node, loop process, query process)
\* so that a node can be retrieved from a process name and vice versa.
\* The spec is parameterized over the node count; the invariants do not
\* prescribe any particular value.

\* Message types: a query, a query reply, and a termination notice.
Message == [kind: {"mq", "mreply", "mterm"}, tgt: Node, src: Node, col: {NoColor, 1, 2}]
Reply == [kind: {"mq", "mreply"}, tgt: Node, src: Node, col: {NoColor, 1, 2}]
Terminate == [kind: "mterm", tgt: NoColor, src: NoColor, col: NoColor]

HostOfLoop(p) == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
HostOfQuery(q) == CHOOSE n \in Node : <<n, NoMessage, q>> \in HostMapping

VARIABLES color, msgs, pc, sample, curIter

vars == <<color, msgs, pc, sample, curIter>>

TypeOK ==
    /\ color \in [Node -> {NoColor, 1, 2}]
    /\ msgs \subseteq Message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"waiting", "running", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ curIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushQueryProcess THEN "running" ELSE "waiting"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ curIter = [p \in SlushLoopProcess |-> 0]

\* The client injects an initial color for an uncolored node; this is the only
\* source of a fresh color and counters the fact that Slush has no quorum.
ClientAssignColor ==
    /\ \E n \in Node, col \in {1, 2} :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<msgs, pc, sample, curIter>>

RequireColor(p) ==
    /\ pc[p] = "waiting"
    /\ color[HostOfLoop(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "running"]
    /\ UNCHANGED <<color, msgs, sample, curIter>>

QuerySampleSet(p) ==
    /\ pc[p] = "running"
    /\ curIter[p] < SlushIterationCount
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ \E Q \in (SUBSET SlushQueryProcess):
         /\ Cardinality(Q) = SampleSetSize
         /\ \A q \in Q : msgs' = msgs \cup {[kind |-> "mq", tgt |-> HostOfQuery(q), src |-> HostOfLoop(p), col |-> color[HostOfLoop(p)]]}
    /\ UNCHANGED <<color, pc, curIter>>

ReplyToQuery ==
    /\ \E m \in msgs :
         /\ m.kind = "mq"
         /\ msgs' = msgs \ {m} \cup {[kind |-> "mreply", tgt |-> m.src, src |-> m.tgt, col |-> IF color[m.tgt] = NoColor THEN m.col ELSE color[m.tgt]]}
    /\ color' = [color EXCEPT ![m.tgt] = IF color[m.tgt] = NoColor THEN m.col ELSE color[m.tgt]]
    /\ UNCHANGED <<pc, sample, curIter>>

TallyReplies(p) ==
    /\ pc[p] = "running"
    /\ \A n \in sample[p] : \E rr \in msgs : rr.kind = "mreply" /\ rr.tgt = HostOfLoop(p) /\ rr.col = color[n]
    /\ \E col \in {1, 2} :
         /\ 2 * Cardinality({n \in sample[p] : color[n] = col}) >= PickFlipThreshold
         /\ color' = [color EXCEPT ![HostOfLoop(p)] = col]
    /\ curIter' = [curIter EXCEPT ![p] = IF curIter[p] < SlushIterationCount THEN curIter[p] + 1 ELSE curIter[p]]
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ UNCHANGED <<msgs, pc>>

LoopTerminate(p) ==
    /\ pc[p] = "running"
    /\ curIter[p] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ msgs' = msgs \cup {Terminate}
    /\ UNCHANGED <<color, sample, curIter>>

QueryLoopExit ==
    /\ \A q \in SlushQueryProcess : pc[q] = "running"
    /\ \A p \in SlushLoopProcess : pc[p] = "done"
    /\ pc' = [q \in SlushQueryProcess |-> "done"]
    /\ UNCHANGED <<color, msgs, sample, curIter>>

Next ==
    \/ ClientAssignColor
    \/ ReplyToQuery
    \/ QueryLoopExit
    \/ \E p \in SlushLoopProcess :
         \/ RequireColor(p) \/ TallyReplies(p) \/ LoopTerminate(p)
         \/ QuerySampleSet(p)
    \/ \E q \in SlushQueryProcess :
         /\ pc[q] = "running" /\ pc' = [pc EXCEPT ![q] = "done"]
         /\ UNCHANGED <<color, msgs, sample, curIter>>

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(ReplyToQuery)
    /\ \A p \in SlushLoopProcess : WF_vars(RequireColor(p)) /\ WF_vars(QuerySampleSet(p)) /\ WF_vars(TallyReplies(p)) /\ WF_vars(LoopTerminate(p))
    /\ SF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

====