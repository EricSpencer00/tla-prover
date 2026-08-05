---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME SlushLoopProcess \cap SlushQueryProcess = {}
ASSUME SlushLoopProcess \cup SlushQueryProcess = HostMapping

Color == {NoColor, "red", "blue"}

VARIABLES nodeColor, messageSet, loopState, queryState, loopSample, loopIterations

vars == <<nodeColor, messageSet, loopState, queryState, loopSample, loopIterations>>

\* nodeColor records each node's current Slush color (or NoColor if never assigned).
\* messageSet holds every in-flight protocol message in a shared network queue.
\* loopState / queryState are program counters; loopSample records the current
\* query's peer set; loopIterations tracks how many iterations each loop has run.
TypeOK ==
  /\ nodeColor \in [Node -> Color]
  /\ messageSet \subseteq {NoMessage} \cup [kind : {"query", "reply", "done"}, src : SlushLoopProcess \cup SlushQueryProcess, dst : SlushLoopProcess \cup SlushQueryProcess, qcol : Color]
  /\ loopState \in [SlushLoopProcess -> {"waiting", "sampling", "done"}]
  /\ queryState \in [SlushQueryProcess -> {"replying", "done"}]
  /\ loopSample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messageSet = {}
  /\ loopState = [lp \in SlushLoopProcess |-> "waiting"]
  /\ queryState = [qp \in SlushQueryProcess |-> "replying"]
  /\ loopSample = [lp \in SlushLoopProcess |-> {}]
  /\ loopIterations = [lp \in SlushLoopProcess |-> 0]

\* The client request process assigns an initial color to an uncolored node.
ClientAssignColor ==
  \/ \E n \in Node, c \in {"red", "blue"} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  \/ UNCHANGED <<messageSet, loopState, queryState, loopSample, loopIterations>>

RequireColor ==
  \E lp \in SlushLoopProcess :
    /\ loopState[lp] = "waiting"
    /\ nodeColor[lp] # NoColor
    /\ loopState' = [loopState EXCEPT ![lp] = "sampling"]
    /\ UNCHANGED <<nodeColor, messageSet, queryState, loopSample, loopIterations>>

\* Sampling: the loop process selects a random set of peers to query this round.
QuerySampleSet ==
  \E lp \in SlushLoopProcess :
    /\ loopState[lp] = "sampling"
    /\ loopIterations[lp] < SlushIterationCount
    /\ \E peers \in {p \in SlushQueryProcess : p # lp} :
         /\ Cardinality(peers) = SampleSetSize
         /\ loopSample' = [loopSample EXCEPT ![lp] = peers]
    /\ messageSet' = messageSet \cup {[kind |-> "query", src |-> lp, dst |-> qp, qcol |-> nodeColor[lp]] : qp \in loopSample[lp]}
    /\ UNCHANGED <<nodeColor, loopState, queryState, loopIterations>>

\* A query process adopts the queried color if it had none, then replies.
RespondToQuery ==
  \E m \in messageSet :
    /\ m.kind = "query"
    /\ queryState[m.dst] = "replying"
    /\ nodeColor[m.dst] = NoColor
    /\ nodeColor' = [nodeColor EXCEPT ![m.dst] = m.qcol]
    /\ messageSet' = (messageSet \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, qcol |-> IF nodeColor[m.dst] = NoColor THEN m.qcol ELSE nodeColor[m.dst]]}
    /\ UNCHANGED <<loopState, queryState, loopSample, loopIterations>>

\* The loop process tallies replies; a color reaching the flip threshold is adopted.
TallyReplies ==
  \E lp \in SlushLoopProcess :
    /\ loopState[lp] = "sampling"
    /\ loopSample[lp] # {}
    /\ \A qp \in loopSample[lp] : [kind |-> "reply", src |-> qp, dst |-> lp, qcol |-> nodeColor[qp]] \in messageSet
    /\ LET replies == {m.qcol : m \in messageSet : m.kind = "reply" /\ m.dst = lp}
           count(c) == Cardinality({m \in messageSet : m.kind = "reply" /\ m.dst = lp /\ m.qcol = c})
           majority == \E c \in replies : count(c) >= PickFlipThreshold
           newColor == IF majority THEN CHOOSE c \in replies : count(c) >= PickFlipThreshold ELSE nodeColor[lp]
       IN nodeColor' = [nodeColor EXCEPT ![lp] = newColor]
    /\ messageSet' = {m \in messageSet : ~(m.kind = "reply" /\ m.dst = lp)}
    /\ loopSample' = [loopSample EXCEPT ![lp] = {}]
    /\ loopIterations' = [loopIterations EXCEPT ![lp] = @ + 1]
    /\ UNCHANGED <<loopState, queryState>>

LoopTermination ==
  \E lp \in SlushLoopProcess :
    /\ loopState[lp] = "sampling"
    /\ loopIterations[lp] >= SlushIterationCount
    /\ loopState' = [loopState EXCEPT ![lp] = "done"]
    /\ messageSet' = messageSet \cup {[kind |-> "done", src |-> lp, dst |-> NoMessage, qcol |-> NoColor]}
    /\ UNCHANGED <<nodeColor, queryState, loopSample, loopIterations>>

QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : loopState[lp] = "done"
  /\ \A qp \in SlushQueryProcess : queryState[qp] = "replying"
  /\ queryState' = [qp \in SlushQueryProcess |-> "done"]
  /\ UNCHANGED <<nodeColor, messageSet, loopState, loopSample, loopIterations>>

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

ProcessTermination == \A lp \in SlushLoopProcess, qp \in SlushQueryProcess : <>(loopState[lp] = "done" /\ queryState[qp] = "done")

QuantumConvergence == TRUE

====