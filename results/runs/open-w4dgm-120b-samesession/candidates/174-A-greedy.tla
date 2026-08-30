---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* A host mapping triple links a node to its loop process and its query process.
HostOf(n) == CHOOSE h \in HostMapping : h[1] = n
LoopOf(n) == CHOOSE h \in HostMapping : h[1] = n /\ h[2]
QueryOf(n) == CHOOSE h \in HostMapping : h[1] = n /\ h[3]

Message == [kind: {"query", "reply", "term"}, src: SlushQueryProcess, dst: SlushLoopProcess, col: {NoColor} \cup (Node \X Node)]

VARIABLES color, inbox, pc, sample, iters

vars == <<color, inbox, pc, sample, iters>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup (Node \X Node)]
  /\ inbox \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (a transaction).
AssignColor ==
  /\ \E n \in Node, c \in (Node \X Node) :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<inbox, pc, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "idle"
       /\ color[HostOf(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, inbox, sample, iters>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ iters[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ inbox' = inbox \cup {[kind |-> "query", src |-> q, dst |-> p, col |-> color[HostOf(p)]] : q \in Q}
       /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<color, iters>>

RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "query"
       /\ LET n == HostOf(m.src) IN
            /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN m.col ELSE color[n]]
            /\ inbox' = (inbox \ {m}) \cup {[kind |-> "reply", src |-> m.src, dst |-> m.dst, col |-> IF color[n] = NoColor THEN m.col ELSE color[n]]}
  /\ UNCHANGED <<pc, sample, iters>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampling"
       /\ \A q \in sample[p] : \E m \in inbox : m.kind = "reply" /\ m.src = q /\ m.dst = p
       /\ LET tallies == [c \in (Node \X Node) |-> Cardinality({m \in inbox : m.kind = "reply" /\ m.dst = p /\ m.col = c})] IN
            /\ color' = [n \in Node |-> IF n = HostOf(p) /\ \E c \in (Node \X Node) : tallies[c] >= PickFlipThreshold THEN c ELSE color[n]]
            /\ inbox' = {m \in inbox : ~(m.kind = "reply" /\ m.dst = p)}
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
            /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ iters[p] = SlushIterationCount
       /\ inbox' = inbox \cup {[kind |-> "term", src |-> NoMessage, dst |-> p, col |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "idle"
       /\ \A p \in SlushLoopProcess : pc[p] = "done"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, inbox, sample, iters>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
  /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====