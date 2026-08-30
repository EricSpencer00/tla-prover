---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

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

MessageDomain == [src: SlushLoopProcess, dst: SlushQueryProcess, phase: {"query", "reply"}, col: Node \cup {NoColor}]

VARIABLES
    nodeColor,
    messageSet,
    pc,
    sample,
    loopIteration

vars == <<nodeColor, messageSet, pc, sample, loopIteration>>

TypeOK ==
    /\ nodeColor \in [Node -> Node \cup {NoColor}]
    /\ messageSet \subseteq MessageDomain
    /\ pc \in [SlushLoopProcess -> {"awaitingColor", "awaitingResponses", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messageSet = {}
    /\ pc = [p \in SlushLoopProcess |-> "awaitingColor"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ loopIteration = [p \in SlushLoopProcess |-> 0]

\* The client is the only source of initial colors; it may be slow but never fails.
AssignColor ==
    \E p \in SlushLoopProcess, n \in Node, col \in Node :
        /\ nodeColor[n] = NoColor
        /\ nodeColor' = [nodeColor EXCEPT ![n] = col]
        /\ UNCHANGED <<messageSet, pc, sample, loopIteration>>

RequireColor ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "awaitingColor"
        /\ \E g \in HostMapping :
            /\ g[1] = p
            /\ nodeColor[g[2]] # NoColor
        /\ pc' = [pc EXCEPT ![p] = "awaitingResponses"]
        /\ UNCHANGED <<nodeColor, messageSet, sample, loopIteration>>

\* The loop process samples peers and sends them its own color to poll.
QuerySampleSet ==
    \E p \in SlushLoopProcess, s \in SUBSET SlushQueryProcess :
        /\ pc[p] = "awaitingResponses"
        /\ Cardinality(s) = SampleSetSize
        /\ sample' = [sample EXCEPT ![p] = s]
        /\ \E g \in HostMapping :
            /\ g[1] = p
            /\ LET col == nodeColor[g[2]] IN
               messageSet' = messageSet \cup { [src |-> p, dst |-> q, phase |-> "query", col |-> col] : q \in s }
        /\ UNCHANGED <<nodeColor, pc, loopIteration>>

\* The query process adopts the query's color if its host is still uncolored, then
\* answers with whatever color its host currently holds.
RespondToQuery ==
    \E m \in messageSet :
        /\ m.phase = "query"
        /\ m.dst # NoMessage
        /\ \E g \in HostMapping :
            /\ g[2] = m.dst
            /\ nodeColor' = IF nodeColor[g[2]] = NoColor THEN [nodeColor EXCEPT ![g[2]] = m.col] ELSE nodeColor
            /\ messageSet' = (messageSet \ {m}) \cup {[src |-> m.src, dst |-> m.dst, phase |-> "reply", col |-> nodeColor[g[2]]]}
        /\ UNCHANGED <<pc, sample, loopIteration>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
        /\ pc[p] = "awaitingResponses"
        /\ sample[p] # {}
        /\ \A q \in sample[p] : [src |-> p, dst |-> q, phase |-> "reply", col |-> NoColor] \notin messageSet
        /\ Cardinality(messageSet) >= Cardinality(sample[p])
        /\ LET replyCount(col) == Cardinality({m \in messageSet : m.src = p /\ m.phase = "reply" /\ m.col = col})
               g == CHOOSE g \in HostMapping : g[1] = p
               newColor == IF replyCount(g[2]) >= PickFlipThreshold THEN g[2] ELSE nodeColor[g[2]]
           IN nodeColor' = [nodeColor EXCEPT ![g[2]] = newColor]
        /\ messageSet' = {m \in messageSet : m.src # p}
        /\ sample' = [sample EXCEPT ![p] = {}]
        /\ loopIteration' = [loopIteration EXCEPT ![p] = @ + 1]
        /\ pc' = [pc EXCEPT ![p] = IF loopIteration[p] + 1 >= SlushIterationCount THEN "done" ELSE "awaitingResponses"]

LoopTerminate ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "awaitingResponses"
        /\ loopIteration[p] >= SlushIterationCount
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ messageSet' = messageSet \cup { [src |-> p, dst |-> NoMessage, phase |-> "reply", col |-> NoColor] }
        /\ UNCHANGED <<nodeColor, sample, loopIteration>>

QueryLoopExit ==
    /\ \A p \in SlushLoopProcess : pc[p] = "done"
    /\ \A q \in SlushQueryProcess : [src |-> NoMessage, dst |-> q, phase |-> "reply", col |-> NoColor] \notin messageSet
    /\ UNCHANGED vars

Next ==
    \/ AssignColor
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ LoopTerminate
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

\* Convergence to a single color is probabilistic and not expressible in TLA+, so the
\* only property we can check here is that the model always reaches a done state.
Termination == \A p \in SlushLoopProcess : pc[p] = "done"

====