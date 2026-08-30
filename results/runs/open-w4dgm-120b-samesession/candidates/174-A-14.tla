---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A message carries the values the two receiver types need: a query needs the
\* sender's color, the other two only need to name their sender and receiver.
Message == [frm: SlushLoopProcess \cup SlushQueryProcess,
            to: SlushLoopProcess \cup SlushQueryProcess,
            col: {NoColor} \cup Node, kind: {"query", "reply", "done"}]

VARIABLES colors, inbox, pc, sample, itersDone

vars == <<colors, inbox, pc, sample, itersDone>>

QueryProcessOf(n) == CHOOSE q \in SlushQueryProcess : <<n, q>> \in HostMapping
LoopProcessOf(n) == CHOOSE l \in SlushLoopProcess : <<n, l>> \in HostMapping

RECURSIVE ColorCount(_, _)
ColorCount(S, c) ==
  IF S = {} THEN 0
  ELSE LET m == CHOOSE x \in S : TRUE IN
       (IF colors[m] = c THEN 1 ELSE 0) + ColorCount(S \ {m}, c)

TypeOK ==
  /\ colors \in [SlushQueryProcess -> {NoColor} \cup Node]
  /\ inbox \in SUBSET Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"client", "waitcolor", "sample",
                                                        "tally", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ itersDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colors = [q \in SlushQueryProcess |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushLoopProcess
                                                             THEN "client" ELSE "waitcolor"]
  /\ sample = [l \in SlushLoopProcess |-> {}]
  /\ itersDone = [l \in SlushLoopProcess |-> 0]

ClientAssignsColor ==
  /\ \E n \in Node :
       /\ colors[QueryProcessOf(n)] = NoColor
       /\ colors' = [colors EXCEPT ![QueryProcessOf(n)] = n]
  /\ UNCHANGED <<pc, inbox, sample, itersDone>>

RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "client"
       /\ colors[LoopProcessOf(l)] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "waitcolor"]
  /\ UNCHANGED <<colors, inbox, sample, itersDone>>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "waitcolor"
       /\ itersDone[l] < SlushIterationCount
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ \A q \in Q : q # QueryProcessOf(LoopProcessOf(l))
            /\ sample' = [sample EXCEPT ![l] = Q]
            /\ inbox' = inbox \cup {[frm |-> l, to |-> q, col |-> colors[LoopProcessOf(l)], kind |-> "query"]
                                      : q \in Q}
       /\ pc' = [pc EXCEPT ![l] = "tally"]
  /\ UNCHANGED <<colors, itersDone>>

RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "query"
       /\ colors[m.to] = NoColor
       /\ colors' = [colors EXCEPT ![m.to] = m.col]
       /\ inbox' = (inbox \ {m}) \cup {[frm |-> m.frm, to |-> m.to, col |-> colors[m.to], kind |-> "reply"]}
  /\ UNCHANGED <<pc, sample, itersDone>>

\* The flip threshold is met or exceeded by one of the two colors.
TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "tally"
       /\ \A q \in sample[l] : \E m \in inbox : m.frm = q /\ m.to = l /\ m.kind = "reply"
       /\ \E c \in Node :
            /\ ColorCount(sample[l], c) >= PickFlipThreshold
            /\ colors' = [colors EXCEPT ![LoopProcessOf(l)] = c]
       /\ inbox' = {m \in inbox : ~(m.kind = "reply" /\ m.to = l)}
       /\ sample' = [sample EXCEPT ![l] = {}]
       /\ itersDone' = [itersDone EXCEPT ![l] = @ + 1]
       /\ pc' = IF itersDone[l] + 1 = SlushIterationCount THEN "done" ELSE "waitcolor"

LoopTermination ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "done"
       /\ pc' = [pc EXCEPT ![l] = "waitcolor"]
       /\ inbox' = inbox \cup {[frm |-> l, to |-> NoMessage, col |-> NoColor, kind |-> "done"]}
  /\ UNCHANGED <<colors, sample, itersDone>>

QueryLoopExit ==
  /\ \A l \in SlushLoopProcess : pc[l] = "waitcolor"
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "waitcolor"
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colors, inbox, sample, itersDone>>

Next ==
  \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet
  \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(ClientAssignsColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
  /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

AllProcessesEventuallyDone == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done")
====