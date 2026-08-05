---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush implements the simplest Snow-family protocol: each node's loop process
\* periodically samples a random subset of peers, collects their responses, and
\* adopts a sufficiently popular opinion (color). Because PlusCal models an
\* infinite loop as a self-loop (rather than terminating it), every loop
\* process is always in some step; termination is signalled by a broadcast
\* message rather than by exiting the process itself.
CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES nodeColor, inFlight, procStep, sampleSet, iterationCount

TypeInvariant ==
    /\ nodeColor \in [Node -> {NoColor, 0, 1}]
    /\ inFlight \subseteq (SlushLoopProcess \X SlushQueryProcess) \cup (SlushQueryProcess \X SlushLoopProcess) \cup (SlushLoopProcess \X {NoMessage})
    /\ procStep \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waiting", "sampling", "collecting", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET (Node \ {NoColor})]
    /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ inFlight = {}
    /\ procStep = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "waiting"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterationCount = [lp \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node at most once.
ClientAssignsColor ==
    /\ procStep["client"] = "waiting"
    /\ \E n \in Node :
        /\ nodeColor[n] = NoColor
        /\ nodeColor' = [nodeColor EXCEPT ![n] = 1 - nodeColor[n]]
    /\ procStep' = [procStep EXCEPT !["client"] = "done"]
    /\ UNCHANGED <<inFlight, sampleSet, iterationCount>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
        /\ procStep[lp] = "waiting"
        /\ nodeColor[(HostMapping \X {lp})[1]] # NoColor
        /\ procStep' = [procStep EXCEPT ![lp] = "sampling"]
    /\ UNCHANGED <<nodeColor, inFlight, sampleSet, iterationCount>>

QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
        /\ procStep[lp] = "sampling"
        /\ iterationCount[lp] < SlushIterationCount
        /\ \E peers \in SUBSET (Node \ {NoColor}):
            /\ peers # {}
            /\ Cardinality(peers) <= SampleSetSize
            /\ inFlight' = inFlight \cup {<<lp, SlushQueryProcess>> \X peers}
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
        /\ procStep' = [procStep EXCEPT ![lp] = "collecting"]
    /\ UNCHANGED <<nodeColor, iterationCount>>

\* A query process adopts the query's color if it is still uncolored.
RespondToQuery ==
    /\ \E qp \in SlushQueryProcess :
        /\ \E lp \in SlushLoopProcess :
            /\ <<lp, qp>> \in inFlight
            /\ inFlight' = (inFlight \ {<<lp, qp>>}) \cup {<<qp, lp>>}
            /\ nodeColor' = [nodeColor EXCEPT ![(HostMapping \X {qp})[1]] = IF nodeColor[(HostMapping \X {qp})[1]] = NoColor THEN nodeColor[(HostMapping \X {lp})[1]] ELSE nodeColor[(HostMapping \X {qp})[1]]]
    /\ UNCHANGED <<procStep, sampleSet, iterationCount>>

TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
        /\ procStep[lp] = "collecting"
        /\ \A peer \in sampleSet[lp] : <<SlushQueryProcess, lp>> \in inFlight
        /\ LET sampleColor == Cardinality({peer \in sampleSet[lp] : nodeColor[peer] = nodeColor[(HostMapping \X {lp})[1]]}) IN
            nodeColor' = IF sampleColor >= PickFlipThreshold THEN [nodeColor EXCEPT ![(HostMapping \X {lp})[1]] = nodeColor[(HostMapping \X {lp})[1]]] ELSE nodeColor
        /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
        /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
        /\ procStep' = [procStep EXCEPT ![lp] = "sampling"]
    /\ UNCHANGED <<inFlight>>

LoopTermination ==
    /\ \E lp \in SlushLoopProcess :
        /\ procStep[lp] = "sampling"
        /\ iterationCount[lp] = SlushIterationCount
        /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
        /\ procStep' = [procStep EXCEPT ![lp] = "done"]
        /\ inFlight' = inFlight \cup {<<lp, NoMessage>>}
    /\ UNCHANGED <<nodeColor, sampleSet>>

QueryLoopExit ==
    /\ \A lp \in SlushLoopProcess : procStep[lp] = "done"
    /\ \E qp \in SlushQueryProcess :
        /\ procStep[qp] = "waiting"
        /\ procStep' = [procStep EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<nodeColor, inFlight, sampleSet, iterationCount>>

Next == ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_<<nodeColor, inFlight, procStep, sampleSet, iterationCount>>

AllProcessesEventuallyDone ==
    (\A p \in SlushLoopProcess \cup SlushQueryProcess : (procStep[p] = "done") ~> (procStep[p] = "done")) /\ (procStep["client"] = "done" ~> procStep["client"] = "done")

====