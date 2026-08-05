---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush: a metastable consensus protocol from the Avalanche family.  Each     *)
(* node runs a loop process that samples a random peer set and adopts any      *)
(* color that reaches the flip threshold.  Because TLA+ has no probabilistic  *)
(* modeling, this PlusCal script is executable pseudocode; convergence to a     *)
(* single color is a probabilistic safety property that cannot be captured     *)
(* here.  What the model can check is structural type-correctness and that     *)
(* every process eventually reaches a terminal state.                           *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping
          SlushIterationCount, SampleSetSize, PickFlipThreshold
          NoColor, NoMessage

ASSUME /\ HostMapping \in [SlushLoopProcess -> Node \cross SlushQueryProcess]
       /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

Message == [from : Node, kind : {"query", "reply", "term"}, color : 0..2]

VARIABLES color, messages, pc, sample, iteration

vars == <<color, messages, pc, sample, iteration>>

TypeInvariant ==
  /\ color \in [Node -> 0..2]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..4]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> IF p = "client" THEN 0 ELSE 1]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* A client transaction colors an uncolored node with a random choice.
ClientAssignsColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node, c \in 1..2 :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<messages, sample, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ LET node == (HostMapping[p]).1 IN
            /\ color[node] # NoColor
            /\ pc' = [pc EXCEPT ![p] = 2]
            /\ UNCHANGED <<color, messages, sample, iteration>>

\* The loop process samples a peer set and broadcasts its current color.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ iteration[p] < SlushIterationCount
       /\ Cardinality(sample[p]) = 0
       /\ LET node == (HostMapping[p]).1 IN
            /\ \E S \in SUBSET (Node \ {node}) :
                 /\ Cardinality(S) = SampleSetSize
                 /\ sample' = [sample EXCEPT ![p] = S]
                 /\ messages' = messages \cup
                      [from |-> node, kind |-> "query", color |-> color[node]]
            /\ UNCHANGED <<color, pc, iteration>>

\* A query process answers with its node's current color, adopting the query
\* color only if it is currently uncolored.
RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ \E q \in SlushQueryProcess :
            /\ (HostMapping[q]).2 = q
            /\ LET node == (HostMapping[q]).1 IN
                 /\ color' = [color EXCEPT ![node] = IF color[node] = NoColor THEN m.color ELSE color[node]]
                 /\ messages' = (messages \ {m}) \cup [from |-> node, kind |-> "reply", color |-> IF color[node] = NoColor THEN m.color ELSE color[node]]
                 /\ UNCHANGED <<pc, sample, iteration>>

\* The loop tallies replies and adopts the majority color when it reaches the
\* flip threshold.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ Cardinality(sample[p]) > 0
       /\ \A q \in sample[p] : \E m \in messages : m.kind = "reply" /\ m.from = q
       /\ LET hist == [c \in 0..2 |-> Cardinality({q \in sample[p] : \E m \in messages : m.kind = "reply" /\ m.from = q /\ m.color = c})]
              node == (HostMapping[p]).1
              newc == IF hist[1] >= PickFlipThreshold THEN 1 ELSE IF hist[2] >= PickFlipThreshold THEN 2 ELSE color[node]
          IN color' = [color EXCEPT ![node] = newc]
       /\ messages' = messages \cup {[from |-> node, kind |-> "term", color |-> 0]}
       /\ pc' = [pc EXCEPT ![p] = 3]
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 3
       /\ pc' = [pc EXCEPT ![p] = 4]
       /\ UNCHANGED <<color, messages, sample, iteration>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 1
       /\ \A p \in SlushLoopProcess : pc[p] = 4
       /\ pc' = [pc EXCEPT ![q] = 2]
       /\ UNCHANGED <<color, messages, sample, iteration>>

Next == /\ \E p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : UNCHANGED <<color, messages, sample, iteration>>
        /\ \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
           \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(RespondToQuery)
  /\ WF_vars(TallyReplies)
  /\ WF_vars(LoopTermination)
  /\ WF_vars(QueryLoopExit)

AllProcessesReachDone ==
  \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : <>_vars(pc[p] = 4)

====