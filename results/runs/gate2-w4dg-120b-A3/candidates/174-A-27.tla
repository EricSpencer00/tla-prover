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

Processes == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

MessageTypes == {"query", "queryReply", "termination"}

VARIABLES
  colorOf,
  inFlight,
  pc,
  sample,
  loopIter

vars == <<colorOf, inFlight, pc, sample, loopIter>>

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ inFlight = {}
  /\ pc = [p \in Processes |-> IF p \in SlushLoopProcess THEN "waitColor" ELSE IF p = "client" THEN "assign" ELSE "reply"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

AssignColor(n) ==
  /\ colorOf[n] = NoColor
  /\ \E c \in {"c1", "c2"} : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ UNCHANGED <<inFlight, pc, sample, loopIter>>

ClientStep ==
  \/ \E n \in Node : AssignColor(n)
  \/ \A n \in Node : colorOf[n] # NoColor
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<colorOf, inFlight, sample, loopIter>>

RequireColor(p) ==
  /\ pc[p] = "waitColor"
  /\ colorOf[HostMapping[p].node] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "sample"]
  /\ UNCHANGED <<colorOf, inFlight, sample, loopIter>>

SendQueries(p) ==
  /\ pc[p] = "sample"
  /\ \E ss \in SUBSET SlushQueryProcess :
       /\ Cardinality(ss) = SampleSetSize
       /\ \A q \in ss : q # HostMapping[p].queryProc
       /\ ss = sample[p]
       /\ inFlight' = inFlight \cup {<<p, q, colorOf[HostMapping[p].node], "query">> : q \in ss}
  /\ pc' = [pc EXCEPT ![p] = "waitReplies"]
  /\ UNCHANGED <<colorOf, sample, loopIter>>

Respond(m) ==
  /\ m \in inFlight
  /\ m[4] = "query"
  /\ LET q == m[2] IN
       /\ inFlight' = (inFlight \ {m}) \cup {<<m[1], q, colorOf[HostMapping[q].node], "queryReply">>}
       /\ colorOf' = IF colorOf[HostMapping[q].node] = NoColor THEN [colorOf EXCEPT ![HostMapping[q].node] = m[3]] ELSE colorOf
  /\ UNCHANGED <<pc, sample, loopIter>>

TallyReplies(p) ==
  /\ pc[p] = "waitReplies"
  /\ \A q \in sample[p] : <<p, q, "queryReply">> \in inFlight
  /\ LET replies == {<<q, colorOf[HostMapping[q].node], "queryReply">> : q \in sample[p]}
         c1 == Cardinality({r \in replies : r[2] = "c1"})
         c2 == Cardinality({r \in replies : r[2] = "c2"})
         newc == IF c1 >= PickFlipThreshold THEN "c1" ELSE IF c2 >= PickFlipThreshold THEN "c2" ELSE colorOf[HostMapping[p].node]
     IN
       /\ colorOf' = [colorOf EXCEPT ![HostMapping[p].node] = newc]
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ loopIter' = [loopIter EXCEPT ![p] = loopIter[p] + 1]
       /\ inFlight' = inFlight \ {<<p, q, "queryReply">> : q \in sample[p]}
       /\ pc' = [pc EXCEPT ![p] = IF loopIter[p] + 1 < SlushIterationCount THEN "sample" ELSE "terminate"]

LoopTerminate(p) ==
  /\ pc[p] = "terminate"
  /\ inFlight' = inFlight \cup {<<p, NoMessage, NoMessage, "termination">>}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<colorOf, sample, loopIter>>

ReplyExit(q) ==
  /\ pc[q] = "reply"
  /\ \A p \in SlushLoopProcess : <<p, q, "termination">> \in inFlight
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colorOf, inFlight, sample, loopIter>>

Next ==
  \/ ClientStep
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : SendQueries(p)
  \/ \E m \in inFlight : Respond(m)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ \E q \in SlushQueryProcess : ReplyExit(q)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ colorOf \in [Node -> {"c1", "c2", NoColor}]
  /\ inFlight \subseteq [SlushLoopProcess \X SlushQueryProcess \X ({"c1", "c2", NoMessage}) \X MessageTypes]
  /\ pc \in [Processes -> {"waitColor", "sample", "waitReplies", "terminate", "reply", "done", "assign"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

====