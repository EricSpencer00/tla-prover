---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* The Slush specification is written in PlusCal and compiled to TLA+.
\* The identifier names below must match exactly the reference .cfg
\* configuration; omission or renaming makes the config uncheckable.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Message == [kind : {"query", "reply", "term"},
            src  : SlushLoopProcess, dst : SlushQueryProcess, col : {NoColor, "red", "blue"}]

VARIABLES
  col, inbox, pc, sample, iters

vars == <<col, inbox, pc, sample, iters>>

Quiescent == {p \in SlushLoopProcess : pc[p] = "done"}

TypeOK ==
  /\ col \in [Node -> {NoColor, "red", "blue"}]
  /\ inbox \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waitLoop", "sample", "tally", "done", "replyLoop", "ready"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ col = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> IF p = "client" THEN "ready" ELSE "waitLoop"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client assigns initial colors to uncolored nodes.
ClientAssignsColor ==
  /\ pc["client"] = "ready"
  /\ \E n \in Node :
       /\ col[n] = NoColor
       /\ \E c \in {"red", "blue"} : col' = [col EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "ready"]
  /\ UNCHANGED <<inbox, iters, sample>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waitLoop"
       /\ \E n \in Node, q \in SlushQueryProcess :
            /\ <<n, p, q>> \in HostMapping
            /\ col[n] # NoColor
            /\ pc' = [pc EXCEPT ![p] = "sample"]
            /\ UNCHANGED <<col, inbox, iters, sample>>

\* The loop process queries a random sample of peers; sampling is
\* nondeterministic here because TLA+ has no random generator.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sample"
       /\ iters[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ Q # {}
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ inbox' = inbox \cup {[kind |-> "query", src |-> p, dst |-> q, col |-> col[CHOOSE n \in Node : <<n, p, q>> \in HostMapping] ] : q \in Q}
       /\ pc' = [pc EXCEPT ![p] = "tally"]
  /\ UNCHANGED <<col, iters>>

\* A query process answers a query and adopts the query's color if it
\* is still uncolored.
RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "query"
       /\ LET n == CHOOSE x \in Node : <<x, m.src, m.dst>> \in HostMapping IN
          /\ col' = [col EXCEPT ![n] = IF col[n] = NoColor THEN m.col ELSE col[n]]
          /\ inbox' = (inbox \ {m}) \cup {[kind |-> "reply", src |-> m.src, dst |-> m.dst, col |-> col[n]]}
       /\ UNCHANGED <<pc, sample, iters>>

\* Tally all sampled replies; a strict majority flips the node's color.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tally"
       /\ \A q \in sample[p] : \E m \in inbox : m.kind = "reply" /\ m.src = p /\ m.dst = q
       /\ LET red == Cardinality({q \in sample[p] : col[CHOOSE n \in Node : <<n, p, q>> \in HostMapping] = "red"})
              blue == Cardinality({q \in sample[p] : col[CHOOSE n \in Node : <<n, p, q>> \in HostMapping] = "blue"}) IN
          col' = IF red >= PickFlipThreshold THEN [col EXCEPT ![CHOOSE n \in Node : <<n, p, CHOOSE q \in sample[p] : TRUE>> \in HostMapping] = "red"]
                 ELSE IF blue >= PickFlipThreshold THEN [col EXCEPT ![CHOOSE n \in Node : <<n, p, CHOOSE q \in sample[p] : TRUE>> \in HostMapping] = "blue"]
                 ELSE col
       /\ inbox' = {m \in inbox : ~(m.kind = "reply" /\ m.src = p)}
       /\ pc' = [pc EXCEPT ![p] = IF iters[p] + 1 = SlushIterationCount THEN "done" ELSE "waitLoop"]
       /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
       /\ sample' = [sample EXCEPT ![p] = {}]

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ inbox' = inbox \cup {[kind |-> "term", src |-> p, dst |-> NoMessage, col |-> NoColor]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<col, iters, sample>>

QueryLoopExit ==
  /\ \A p \in SlushQueryProcess :
       pc[p] = "replyLoop"
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "done" : p \in SlushQueryProcess]
  /\ UNCHANGED <<col, inbox, iters, sample>>

Next ==
  \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)

Quiescence == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

TypeInvariant == TypeOK

====