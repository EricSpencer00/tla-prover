---- MODULE Slush ----
EXTENDS Integers, FiniteSets

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

QueryMessages == [kind: {"query"}, to: SlushQueryProcess, from: SlushLoopProcess, color: Node \cup {NoColor}]
QueryReplyMessages == [kind: {"reply"}, to: SlushLoopProcess, from: SlushQueryProcess, color: Node \cup {NoColor}]
TerminateMessages == [kind: {"term"}, to: SlushLoopProcess]

VARIABLES color, inbox, programCounter, sampleSet, loopsCompleted

Vars == <<color, inbox, programCounter, sampleSet, loopsCompleted>>

TypeOK ==
    /\ color \in [Node -> Node \cup {NoColor}]
    /\ inbox \subseteq (QueryMessages \cup QueryReplyMessages \cup TerminateMessages)
    /\ programCounter \in [SlushLoopProcess -> {"waiting", "sampling", "tallying", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopsCompleted \in [SlushLoopProcess -> 0..SlushIterationCount]

\* Slush is a metastable protocol: the color assignment only settles once a
\* majority of sampled peers agrees. The spec is not a probability model, so
\* convergence is not verified here -- only that the assignment stays typed.
TypeInvariant == TypeOK

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ programCounter = [p \in SlushLoopProcess |-> "waiting"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopsCompleted = [p \in SlushLoopProcess |-> 0]

HostOfLoop(p) == CHOOSE n \in Node : <<n, p, NoMessage>> \in HostMapping
HostOfQuery(q) == CHOOSE n \in Node : <<n, NoMessage, q>> \in HostMapping

\* The client front-end assigns initial colors to uncolored nodes; Slush has
\* no notion of a transaction pool, so this is the one external entry point.
ClientAssignsColor(n, col) ==
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<inbox, programCounter, sampleSet, loopsCompleted>>

RequireColor(p) ==
    /\ programCounter[p] = "waiting"
    /\ color[HostOfLoop(p)] # NoColor
    /\ programCounter' = [programCounter EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<color, inbox, sampleSet, loopsCompleted>>

QuerySampleSet(p) ==
    /\ programCounter[p] = "sampling"
    /\ \E Q \in SUBSET SlushQueryProcess :
         /\ Cardinality(Q) = SampleSetSize
         /\ Q # {}
         /\ sampleSet' = [sampleSet EXCEPT ![p] = Q]
         /\ inbox' = inbox \cup { [kind |-> "query", to |-> q, from |-> p, color |-> color[HostOfLoop(p)]] : q \in Q }
    /\ UNCHANGED <<color, programCounter, loopsCompleted>>

RespondToQuery(msg) ==
    /\ msg.kind = "query"
    /\ msg \in inbox
    /\ inbox' = (inbox \ {msg}) \cup
         { [kind |-> "reply", to |-> msg.from, from |-> msg.to,
              color |-> IF color[HostOfQuery(msg.to)] = NoColor THEN msg.color ELSE color[HostOfQuery(msg.to)]] }
    /\ color' = [color EXCEPT ![HostOfQuery(msg.to)] = IF color[HostOfQuery(msg.to)] = NoColor THEN msg.color ELSE color[HostOfQuery(msg.to)]]
    /\ UNCHANGED <<programCounter, sampleSet, loopsCompleted>>

TallyReplies(p) ==
    /\ programCounter[p] = "sampling"
    /\ \A q \in sampleSet[p] : [kind |-> "reply", to |-> p, from |-> q, color |-> NoColor] \in inbox
    /\ LET replies == {r \in inbox : r.kind = "reply" /\ r.to = p}
           colA == {r \in replies : r.color = CHOOSE n \in Node : TRUE}
           colB == replies \ colA
           flipA == (Cardinality(colA) >= PickFlipThreshold) /\ (color[HostOfLoop(p)] # CHOOSE n \in Node : TRUE)
           flipB == (Cardinality(colB) >= PickFlipThreshold) /\ (color[HostOfLoop(p)] # NoColor /\ color[HostOfLoop(p)] # CHOOSE n \in Node : TRUE)
       IN
         /\ color' = IF flipA THEN [color EXCEPT ![HostOfLoop(p)] = CHOOSE n \in Node : TRUE]
                     ELSE IF flipB THEN [color EXCEPT ![HostOfLoop(p)] = NoColor]
                     ELSE color
         /\ inbox' = inbox \ replies
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ loopsCompleted' = [loopsCompleted EXCEPT ![p] = IF loopsCompleted[p] < SlushIterationCount THEN loopsCompleted[p] + 1 ELSE loopsCompleted[p]]
    /\ programCounter' = IF loopsCompleted[p] = SlushIterationCount THEN "done" ELSE programCounter[p]

LoopTermination(p) ==
    /\ programCounter[p] = "done"
    /\ [kind |-> "term", to |-> p] \notin inbox
    /\ inbox' = inbox \cup { [kind |-> "term", to |-> p] }
    /\ UNCHANGED <<color, programCounter, sampleSet, loopsCompleted>>

QueryLoopExit(q) ==
    /\ \A p \in SlushLoopProcess : [kind |-> "term", to |-> p] \in inbox
    /\ programCounter' = [p \in SlushLoopProcess |-> IF programCounter[p] = "done" THEN "done" ELSE programCounter[p]]
    /\ UNCHANGED <<color, inbox, sampleSet, loopsCompleted>>

Next ==
    \/ \E n \in Node, col \in Node \cup {NoColor} : ClientAssignsColor(n, col)
    \/ \E p \in SlushLoopProcess : RequireColor(p)
    \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
    \/ \E msg \in inbox : RespondToQuery(msg)
    \/ \E p \in SlushLoopProcess : TallyReplies(p)
    \/ \E p \in SlushLoopProcess : LoopTermination(p)
    \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_Vars
Terminate ==
    /\ \A p \in SlushLoopProcess : programCounter[p] = "done"
    /\ \A q \in SlushQueryProcess : programCounter[q] = "done"

Termination == Terminate
====