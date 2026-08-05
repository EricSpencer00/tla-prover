---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush implements the simplest member of the Snow family of
\* probabilistic consensus protocols: loop processes repeatedly sample a
\* subset of peers and adopt a sufficiently popular opinion. Since TLA+ has
\* no random generation, this is an executable sketch rather than a
\* faithful probabilistic model.
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

\* Names of all messages in flight; each carries a sender, a destination, and
\* the color being reported, and they are pulled from an unordered set.
VARIABLES
    assignment,
    messages,
    pc,
    sampleSet,
    iterationCount

vars == <<assignment, messages, pc, sampleSet, iterationCount>>

Message == [to: SlushQueryProcess, from: SlushLoopProcess, color: Node \cup {NoColor}]
QueryMessage == [to: SlushQueryProcess, from: SlushLoopProcess, color: Node \cup {NoColor}]
QueryReply == [to: SlushLoopProcess, from: SlushQueryProcess, color: Node \cup {NoColor}]
TerminationMessage == [to: SlushQueryProcess, from: SlushLoopProcess]

TypeOK ==
    /\ assignment \in [Node -> Node \cup {NoColor}]
    /\ messages \subseteq QueryMessage \cup QueryReply \cup TerminationMessage
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {SlushClientProcess} -> {"waiting", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ assignment = [v \in Node |-> NoColor]
    /\ messages = {}
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iterationCount = [p \in SlushLoopProcess |-> 0]
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {SlushClientProcess} |-> IF p \in SlushQueryProcess THEN "waiting" ELSE "waiting"]

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor ==
    /\ pc[SlushClientProcess] = "waiting"
    /\ \E v \in Node, col \in Node :
         /\ assignment[v] = NoColor
         /\ assignment' = [assignment EXCEPT ![v] = col]
    /\ UNCHANGED <<messages, pc, sampleSet, iterationCount>>

\* A loop process cannot begin until its host node has been assigned a color.
RequireColor ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "waiting"
         /\ \E v \in Node : <<p, v>> \in HostMapping /\ assignment[v] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "active"]
    /\ UNCHANGED <<assignment, messages, sampleSet, iterationCount>>

\* The loop process selects a random subset of peers and queries their color.
QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "active"
         /\ iterationCount[p] < SlushIterationCount
         /\ \E v \in Node, col \in Node \cup {NoColor} :
              /\ <<p, v>> \in HostMapping
              /\ col = assignment[v]
              /\ \E Q \in SUBSET SlushQueryProcess :
                   /\ Cardinality(Q) = SampleSetSize
                   /\ \A q \in Q : <<p, q>> \in HostMapping
                   /\ messages' = messages \cup {[to |-> q, from |-> p, color |-> col] : q \in Q}
         /\ sampleSet' = [sampleSet EXCEPT ![p] = Q]
    /\ UNCHANGED <<assignment, pc, iterationCount>>

\* A query process adopts the sender's color if uncolored, then replies.
RespondToQuery ==
    /\ \E m \in messages :
         /\ m \in QueryMessage
         /\ [to |-> m.to, from |-> m.from, color |-> m.color] \in messages
         /\ \E col \in Node \cup {NoColor} :
              /\ <<m.to, col>> \in HostMapping
              /\ col' = IF assignment[col] = NoColor THEN m.color ELSE assignment[col]
              /\ assignment' = [assignment EXCEPT ![col] = col']
         /\ messages' = (messages \ {m}) \cup {[to |-> m.from, from |-> m.to, color |-> col']}
    /\ UNCHANGED <<pc, sampleSet, iterationCount>>

\* After collecting all replies, the loop process adopts a majority color if it
\* reaches the flip threshold.
TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "active"
         /\ sampleSet[p] # {}
         /\ iterationCount[p] < SlushIterationCount
         /\ \A q \in sampleSet[p] : [to |-> p, from |-> q, color |-> NoColor] \in messages
         /\ \E col \in Node :
              /\ Cardinality({q \in sampleSet[p] : [to |-> p, from |-> q, color |-> col] \in messages}) >= PickFlipThreshold
              /\ assignment' = [assignment EXCEPT ![HostMapping[p][1]] = col]
         /\ messages' = messages \ {[to |-> p, from |-> q, color |-> NoColor] : q \in sampleSet[p]}
         /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
         /\ iterationCount' = [iterationCount EXCEPT ![p] = iterationCount[p] + 1]
    /\ UNCHANGED pc

\* A loop process that has completed all of its iterations broadcasts a
\* termination message to every query process.
LoopTermination ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] \in {"active", "waiting"}
         /\ iterationCount[p] = SlushIterationCount
         /\ messages' = {m \in messages : ~(m \in TerminationMessage /\ m.from = p)} \cup {[to |-> q, from |-> p] : q \in SlushQueryProcess}
         /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<assignment, sampleSet, iterationCount>>

\* Query processes close their reply loops once all loop processes have
\* terminated.
QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
         /\ pc[q] = "waiting"
         /\ \A p \in SlushLoopProcess : [to |-> q, from |-> p] \in messages
         /\ pc' = [pc EXCEPT ![q] = "done"]
         /\ messages' = {m \in messages : m \notin TerminationMessage \/ m.from # q}
    /\ UNCHANGED <<assignment, sampleSet, iterationCount>>

Next ==
    \/ ClientAssignColor
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ LoopTermination
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllProcessesTerminate == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {SlushClientProcess} : pc[p] = "done"

====