---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* A host mapping triple links a node to its loop process and its query process.
Hosts == {p \in HostMapping : p[1] \in Node /\ p[2] \in SlushLoopProcess /\ p[3] \in SlushQueryProcess}

\* A query message carries the sender's current color; a reply carries the
\* responder's current color.  A termination message has no payload.
Message == [kind: {"query", "reply", "term"}, src: SlushLoopProcess \cup SlushQueryProcess, dst: SlushLoopProcess \cup SlushQueryProcess, col: {NoColor} \cup (NoColor \X NoColor)]

VARIABLES color, inbox, pc, sample, iters

vars == <<color, inbox, pc, sample, iters>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup (NoColor \X NoColor)]
  /\ inbox \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting", "querying", "tallying", "done"}]
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
  /\ \E n \in Node, c \in (NoColor \X NoColor) :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<inbox, pc, sample, iters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "idle"
       /\ \E n \in Node : \A q \in SlushQueryProcess : <<n, p, q>> \in Hosts
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, inbox, sample, iters>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waiting"
       /\ iters[p] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ \A q \in Q : \E n \in Node : <<n, p, q>> \in Hosts
            /\ sample' = [sample EXCEPT ![p] = Q]
            /\ inbox' = inbox \cup {[kind |-> "query", src |-> p, dst |-> q, col |-> color[n]] : q \in Q}
       /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<color, iters>>

RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "query"
       /\ pc[m.dst] = "idle"
       /\ \E n \in Node : <<n, m.src, m.dst>> \in Hosts
       /\ LET newcol == IF color[n] = NoColor THEN m.col ELSE color[n] IN
            /\ color' = [color EXCEPT ![n] = newcol]
            /\ inbox' = (inbox \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> newcol]}
       /\ pc' = [pc EXCEPT ![m.dst] = "replying"]
  /\ UNCHANGED <<sample, iters>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ \A q \in sample[p] : \E m \in inbox : m.kind = "reply" /\ m.src = q /\ m.dst = p
       /\ LET tally(c) == Cardinality({q \in sample[p] : \E m \in inbox : m.kind = "reply" /\ m.src = q /\ m.dst = p /\ m.col = c}) IN
            /\ color' = [n \in Node |-> IF \E q \in SlushQueryProcess : <<n, p, q>> \in Hosts /\ tally(color[n]) >= PickFlipThreshold THEN color[n] ELSE color[n]]
       /\ inbox' = {m \in inbox : ~(m.kind = "reply" /\ m.dst = p)}
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
       /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tallying"
       /\ iters[p] = SlushIterationCount
       /\ inbox' = inbox \cup {[kind |-> "term", src |-> p, dst |-> NoMessage, col |-> NoColor]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "idle"
       /\ \A p \in SlushLoopProcess : pc[p] = "done"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, inbox, sample, iters>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====