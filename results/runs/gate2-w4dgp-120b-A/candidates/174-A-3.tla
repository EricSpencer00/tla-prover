---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES assignment, messages, pc, querySet, iterationCount

vars == <<assignment, messages, pc, querySet, iterationCount>>

Phase == {"querying", "replying", "done"}

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ querySet = [p \in SlushLoopProcess |-> {}]
  /\ iterationCount = [p \in SlushLoopProcess |-> 0]
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"SlushClientProcess"} |-> IF p \in SlushLoopProcess THEN "replying" ELSE "done"]

AssignColor ==
  /\ pc["SlushClientProcess"] = "done"
  /\ \E n \in Node :
       /\ assignment[n] = NoColor
       /\ \E c \in {c1, c2} : assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, querySet, iterationCount, pc>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "replying"
       /\ assignment[HostMapping[p].target] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<assignment, messages, querySet, iterationCount>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ querySet' = [querySet EXCEPT ![p] = Q]
            /\ messages' = messages \cup { [target |-> q, state |-> "SlushQueryMessage", data |-> assignment[HostMapping[p].target]] : q \in Q }
  /\ UNCHANGED <<assignment, iterationCount, pc>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.state = "SlushQueryMessage"
       /\ LET qp == m.target IN
            /\ messages' = (messages \ {m}) \cup { [target |-> HostMapping[qp].host, state |-> "SlushQueryReplyMessage", data |-> assignment[HostMapping[qp].target]] }
            /\ assignment' = [assignment EXCEPT ![HostMapping[qp].target] = IF assignment[HostMapping[qp].target] = NoColor THEN m.data ELSE assignment[HostMapping[qp].target]]
  /\ UNCHANGED <<pc, querySet, iterationCount>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "querying"
       /\ querySet[p] # {}
       /\ \A q \in querySet[p] : \E m \in messages : m.state = "SlushQueryReplyMessage" /\ m.target = HostMapping[q].host /\ m.data = assignment[HostMapping[p].target]
       /\ LET count(c) == Cardinality({q \in querySet[p] : \E m \in messages : m.state = "SlushQueryReplyMessage" /\ m.target = HostMapping[q].host /\ m.data = c})
          IN assignment' = IF count(assignment[HostMapping[p].target]) >= PickFlipThreshold THEN assignment ELSE [assignment EXCEPT ![HostMapping[p].target] = assignment[HostMapping[p].target]]
       /\ querySet' = [querySet EXCEPT ![p] = {}]
       /\ iterationCount' = [iterationCount EXCEPT ![p] = iterationCount[p] + 1]
       /\ messages' = {m \in messages : m.state # "SlushQueryReplyMessage"}
       /\ pc' = IF iterationCount[p] + 1 >= SlushIterationCount THEN [pc EXCEPT ![p] = "done"] ELSE pc
  /\ UNCHANGED <<>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ [target |-> p, state |-> "LoopTerminationMessage", data |-> NoMessage] \notin messages
       /\ messages' = messages \cup { [target |-> p, state |-> "LoopTerminationMessage", data |-> NoMessage] }
  /\ UNCHANGED <<assignment, querySet, iterationCount, pc>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A p \in SlushQueryProcess : pc[p] = "done"
  /\ UNCHANGED vars

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ assignment \in [Node -> {NoColor, c1, c2}]
  /\ \A m \in messages : m.state \in {"SlushQueryMessage", "SlushQueryReplyMessage", "LoopTerminationMessage"}

Termination ==
  \A p \in SlushLoopProcess \cup SlushQueryProcess : (pc[p] = "replying") ~> (pc[p] = "done")
====