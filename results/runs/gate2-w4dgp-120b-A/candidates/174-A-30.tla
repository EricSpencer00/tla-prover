---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES assigned, msgSet, pc, sampleSet, iterationCount

vars == <<assigned, msgSet, pc, sampleSet, iterationCount>>

\* A query message targets the query process of a node and carries the sender's
\* current color; a reply returns that color to the originating loop process.
Message == [type : {"query", "reply", "termination"}, to : SlushQueryProcess \cup SlushLoopProcess, from : SlushLoopProcess \cup SlushQueryProcess, color : {NoColor} \cup (Node \times Node)]

LoopProcessOf(n) == CHOOSE lp \in SlushLoopProcess : [node |-> n] \in HostMapping
QueryProcessOf(n) == CHOOSE qp \in SlushQueryProcess : [node |-> n] \in HostMapping

TypeOK ==
  /\ assigned \in [Node -> {NoColor} \cup Node]
  /\ msgSet \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "waiting", "sampling", "tallying", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assigned = [n \in Node |-> NoColor]
  /\ msgSet = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "idle"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterationCount = [lp \in SlushLoopProcess |-> 0]

PickClientColor(n, c) ==
  /\ pc["client"] = "idle"
  /\ assigned[n] = NoColor
  /\ assigned' = [assigned EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "idle"]
  /\ UNCHANGED <<msgSet, sampleSet, iterationCount>>

Requirement ==
  /\ pc["client"] = "idle"
  /\ pc' = [pc EXCEPT !["client"] = "ready"]
  /\ UNCHANGED <<assigned, msgSet, sampleSet, iterationCount>>

RequireLoop(lp) ==
  /\ pc[lp] = "idle"
  /\ assigned[HostMapping[lp].node] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "waiting"]
  /\ UNCHANGED <<assigned, msgSet, sampleSet, iterationCount>>

\* The loop process selects a random SAMPLESETSIZE-sized set of peers to query.
QuerySampleSet(lp, s) ==
  /\ pc[lp] = "waiting"
  /\ s \subseteq SlushQueryProcess
  /\ Cardinality(s) = SampleSetSize
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = s]
  /\ msgSet' = msgSet \cup {[type |-> "query", to |-> p, from |-> lp, color |-> assigned[HostMapping[lp].node]} : p \in s]
  /\ pc' = [pc EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<assigned, iterationCount>>

RespondQuery(qp) ==
  /\ \E m \in msgSet :
       /\ m.type = "query"
       /\ m.to = qp
       /\ msgSet' = (msgSet \ {m}) \cup {[type |-> "reply", to |-> m.from, from |-> qp, color |-> assigned[HostMapping[qp].node]]}
  /\ UNCHANGED <<assigned, pc, sampleSet, iterationCount>>

\* Replies from the entire sample must arrive before the node may flip.
TallyReplies(lp) ==
  /\ pc[lp] = "sampling"
  /\ Cardinality({m \in msgSet : m.type = "reply" /\ m.to = lp /\ m.from \in sampleSet[lp]}) = SampleSetSize
  /\ LET replyColors == {m \in msgSet : m.type = "reply" /\ m.to = lp /\ m.from \in sampleSet[lp]}
         majorityColor ==
           CHOOSE c \in Node :
             2 * Cardinality({m \in replyColors : m.color[2] = c}) >= PickFlipThreshold
     IN assigned' = [assigned EXCEPT ![HostMapping[lp].node] = majorityColor]
  /\ msgSet' = msgSet \ {m \in msgSet : m.type = "reply" /\ m.to = lp}
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
  /\ pc' = [pc EXCEPT ![lp] = IF iterationCount[lp] + 1 >= SlushIterationCount THEN "done" ELSE "waiting"]

LoopTermination(lp) ==
  /\ pc[lp] = "done"
  /\ ~ \E m \in msgSet : m.type = "termination" /\ m.to = lp
  /\ msgSet' = msgSet \cup {[type |-> "termination", to |-> lp, from |-> NoMessage, color |-> NoMessage]}
  /\ UNCHANGED <<assigned, pc, sampleSet, iterationCount>>

QueryLoopExit(qp) ==
  /\ pc[qp] = "idle"
  /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<assigned, msgSet, sampleSet, iterationCount>>

Next ==
  \/ \E n \in Node, c \in Node : PickClientColor(n, c)
  \/ Requirement
  \/ \E lp \in SlushLoopProcess : RequireLoop(lp) \/ TallyReplies(lp) \/ LoopTermination(lp)
  \/ \E lp \in SlushLoopProcess, s \in SUBSET SlushQueryProcess : QuerySampleSet(lp, s)
  \/ \E qp \in SlushQueryProcess : RespondQuery(qp) \/ QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars

AllProcessesAndClientTerminate ==
  <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done")

====