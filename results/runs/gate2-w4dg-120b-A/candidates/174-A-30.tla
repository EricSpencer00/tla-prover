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

MessageType == [kind: {"query", "reply", "term"}, src: SlushLoopProcess, dst: SlushQueryProcess, col: Node \cup {NoColor}]
ProcessStep == {"awaitColor", "idle", "done"}
QueryStep == {"replyLoop", "done"}

VARIABLES assignment, msgs, lpStep, qpStep, sampleSet, lpIters

vars == <<assignment, msgs, lpStep, qpStep, sampleSet, lpIters>>

TypeInvariant ==
  /\ assignment \in [Node -> Node \cup {NoColor}]
  /\ msgs \subseteq MessageType
  /\ lpStep \in [SlushLoopProcess -> ProcessStep]
  /\ qpStep \in [SlushQueryProcess -> QueryStep]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ lpIters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ lpStep = [p \in SlushLoopProcess |-> "awaitColor"]
  /\ qpStep = [q \in SlushQueryProcess |-> "replyLoop"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ lpIters = [p \in SlushLoopProcess |-> 0]

\* The client transaction that seeds Slush with an initial color
ClientAssignColor ==
  /\ \E n \in Node :
       /\ assignment[n] = NoColor
       /\ \E c \in Node \ {n} : assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, lpStep, qpStep, sampleSet, lpIters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ lpStep[p] = "awaitColor"
       /\ \E n \in Node : <<p, n>> \in HostMapping /\ assignment[n] # NoColor
       /\ lpStep' = [lpStep EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<assignment, msgs, qpStep, sampleSet, lpIters>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ lpStep[p] = "idle"
       /\ lpIters[p] < SlushIterationCount
       /\ \E Y \in SUBSET Node :
            /\ Y \subseteq Node
            /\ Cardinality(Y) = SampleSetSize
            /\ \A q \in SlushQueryProcess : <<p, q>> \in HostMapping => q \in Y
            /\ sampleSet' = [sampleSet EXCEPT ![p] = Y]
            /\ msgs' = msgs \cup {[kind |-> "query", src |-> p, dst |-> q, col |-> assignment[CHOOSE n \in Node : <<p, n>> \in HostMapping]]
                                 : q \in Y}
  /\ UNCHANGED <<assignment, lpStep, qpStep, lpIters>>

\* QueryProcess adopts the query's color if it is still uncolored, then replies
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ qpStep[m.dst] = "replyLoop"
       /\ LET n == CHOOSE n \in Node : <<m.src, n>> \in HostMapping
          IN /\ assignment' = [assignment EXCEPT ![n] = IF assignment[n] = NoColor THEN m.col ELSE assignment[n]]
             /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", src |-> m.src, dst |-> m.dst, col |-> assignment[n]]}
  /\ UNCHANGED <<lpStep, qpStep, sampleSet, lpIters>>

\* The loop process commits a flip once the sampled majority agrees
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ lpStep[p] = "idle"
       /\ \E f \in {a \in (sampleSet[p] \cup {NoColor}) : Cardinality({m \in msgs : m.kind = "reply" /\ m.src = p /\ m.col = a}) >= PickFlipThreshold} :
            /\ assignment' = [assignment EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = f]
       /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.src = p)}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ lpIters' = [lpIters EXCEPT ![p] = IF lpIters[p] < SlushIterationCount THEN lpIters[p] + 1 ELSE lpIters[p]]
  /\ UNCHANGED <<qpStep>>

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ lpStep[p] \in {"idle", "awaitColor"}
       /\ lpIters[p] = SlushIterationCount
       /\ lpStep' = IF lpStep[p] = "awaitColor" THEN [lpStep EXCEPT ![p] = "idle"] ELSE [lpStep EXCEPT ![p] = "done"]
       /\ msgs' = msgs \cup {[kind |-> "term", src |-> p, dst |-> NoMessage, col |-> NoColor]}
  /\ UNCHANGED <<assignment, qpStep, sampleSet, lpIters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ qpStep[q] = "replyLoop"
       /\ \A p \in SlushLoopProcess : lpStep[p] = "done"
       /\ qpStep' = [qpStep EXCEPT ![q] = "done"]
  /\ UNCHANGED <<assignment, msgs, lpStep, sampleSet, lpIters>>

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

\* Termination is reachable: all processes eventually reach a done state
ProcessTermination == <>(\A p \in SlushLoopProcess : lpStep[p] = "done")
                      /\ <>(\A q \in SlushQueryProcess : qpStep[q] = "done")

====