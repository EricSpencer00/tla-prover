---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush consensus protocol from the Avalanche whitepaper.  A node's   *)
(* loop process samples a random peer set each iteration and adopts a       *)
(* sufficiently popular color; this PlusCal spec serves as executable       *)
(* pseudocode (no probabilistic semantics in TLA+).                         *)

CONSTANTS
    Node,               \* all nodes in the network (finite)
    SlushLoopProcess,   \* the per-node loop processes
    SlushQueryProcess,  \* the per-node query processes
    HostMapping,        \* mapping of processes to the node they belong to
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,            \* uncolored sentinel
    NoMessage           \* empty inbox sentinel

\* A Loop or Query process belongs to exactly one node, so the host mapping
\* is a function from process to node; the pairings are the projection.
HostOf(p) == CHOOSE n \in Node : <<p, n>> \in HostMapping

\* Messages are inspected by the receiving process's host node.
Query == [qtype: "query", sink: SlushQueryProcess, src: SlushLoopProcess,
           color: {NoColor} \cup Node]
Reply == [qtype: "reply", sink: SlushLoopProcess, src: SlushQueryProcess,
           color: {NoColor} \cup Node]
Terminate == [qtype: "terminate", sink: SlushLoopProcess, src: NoMessage,
              color: {NoColor}]

ASSUME NoMessage \notin SlushLoopProcess
ASSUME PickFlipThreshold \in Nat

VARIABLES color, inbox, pc, sampleSet, iterationCount

vars == <<color, inbox, pc, sampleSet, iterationCount>>

TypeOK ==
    /\ color \in [Node -> {NoColor} \cup Node]
    /\ inbox \subseteq (Query \cup Reply \cup Terminate)
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "running", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iterationCount = [p \in SlushLoopProcess |-> 0]

LoopDone == \A p \in SlushLoopProcess : pc[p] = "done"
QueryDone == \A q \in SlushQueryProcess : pc[q] = "done"

\* The client assigns an initial color to an uncolored node; it may be slow
\* but never fails, so this can always make progress when colors remain.
AssignColor ==
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ \E c \in Node : color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT ![q \in SlushQueryProcess |-> "running"]]
    /\ UNCHANGED <<inbox, sampleSet, iterationCount>>

RequireColor ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "idle"
         /\ color[HostOf(p)] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "running"]
    /\ UNCHANGED <<color, inbox, sampleSet, iterationCount>>

QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "running"
         /\ sampleSet[p] = {}
         /\ iterationCount[p] < SlushIterationCount
         /\ \E Q \in SUBSET SlushQueryProcess :
              /\ Cardinality(Q) = SampleSetSize
              /\ Q \subseteq (SlushQueryProcess \ {HostOf(p)})
              /\ sampleSet' = [sampleSet EXCEPT ![p] = Q]
              /\ inbox' = inbox \cup {
                   [qtype |-> "query", sink |-> q, src |-> p,
                    color |-> {color[HostOf(p)]}]
                   : q \in Q
               }
    /\ UNCHANGED <<color, pc, iterationCount>>

RespondToQuery ==
    /\ \E m \in inbox :
         /\ m.qtype = "query"
         /\ m.sink = HostOf(m.sink)
         /\ inbox' = (inbox \ {m}) \cup {
              [qtype |-> "reply", sink |-> m.src, src |-> m.sink,
               color |-> {IF color[HostOf(m.sink)] = NoColor THEN Head(m.color) ELSE color[HostOf(m.sink)]}]
           }
         /\ color' = IF color[HostOf(m.sink)] = NoColor
                     THEN [color EXCEPT ![HostOf(m.sink)] = Head(m.color)]
                     ELSE color
    /\ UNCHANGED <<pc, sampleSet, iterationCount>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "running"
         /\ sampleSet[p] # {}
         /\ \A q \in sampleSet[p] : [qtype |-> "reply", sink |-> p, src |-> q, color |-> {NoColor}] \in inbox
         /\ LET seen == {m.color : m \in inbox /\ m.sink = p}
                cCount(c) == Cardinality({x \in seen : x = {c}})
            IN color' = [color EXCEPT ![HostOf(p)] =
                  IF \E c \in Node : cCount(c) >= PickFlipThreshold THEN
                      CHOOSE c \in Node : cCount(c) >= PickFlipThreshold
                  ELSE color[HostOf(p)]]
         /\ inbox' = inbox \ {[qtype |-> "reply", sink |-> p, src |-> q, color |-> {NoColor}]
                                  : q \in sampleSet[p]}
         /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
         /\ iterationCount' = [iterationCount EXCEPT ![p] = iterationCount[p] + 1]
    /\ UNCHANGED pc

LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "running"
         /\ iterationCount[p] = SlushIterationCount
         /\ pc' = [pc EXCEPT ![p] = "done"]
         /\ inbox' = inbox \cup {[qtype |-> "terminate", sink |-> p, src |-> NoMessage, color |-> {NoColor}]}
    /\ UNCHANGED <<color, sampleSet, iterationCount>>

QueryLoopExit ==
    /\ LoopDone
    /\ \A q \in SlushQueryProcess : pc[q] = "idle"
    /\ pc' = [pc EXCEPT ![q \in SlushQueryProcess] = "done"]
    /\ UNCHANGED <<color, inbox, sampleSet, iterationCount>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

GracefulTerminate == LoopDone /\ QueryDone

====