---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

\* Slush is a metastable (probabilistic) protocol.  TLA+ has no notion of
\* probability, so this spec is an executable description -- it cannot prove
\* convergence, only structural facts like type safety and termination.
CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

Message == [src: SlushLoopProcess, dst: SlushQueryProcess, kind: {"query"}, col: Node \cup {NoColor}]
           \cup [src: SlushQueryProcess, dst: SlushLoopProcess, kind: {"reply"}, col: Node \cup {NoColor}]
           \cup [src: SlushLoopProcess, dst: SlushLoopProcess, kind: {"done"}, col: NoColor]

VARIABLES
    color, messages, loopPC, queryPC, sampleSet, loopIter

vars == <<color, messages, loopPC, queryPC, sampleSet, loopIter>>

TypeInvariant ==
    /\ color \in [Node -> Node \cup {NoColor}]
    /\ messages \subseteq Message
    /\ loopPC \in [SlushLoopProcess -> {"idle", "query", "tally", "done"}]
    /\ queryPC \in [SlushQueryProcess -> {"replyLoop", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ loopPC = [p \in SlushLoopProcess |-> "idle"]
    /\ queryPC = [q \in SlushQueryProcess |-> "replyLoop"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopIter = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to one uncolored node.
ClientAssignColor ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in Node \ {n} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, loopPC, queryPC, sampleSet, loopIter>>

RequireColor ==
    \E p \in SlushLoopProcess :
        /\ loopPC[p] = "idle"
        /\ \E n \in Node :
             /\ <<n, p>> \in HostMapping
             /\ color[n] # NoColor
        /\ loopPC' = [loopPC EXCEPT ![p] = "query"]
    /\ UNCHANGED <<color, messages, queryPC, sampleSet, loopIter>>

QuerySampleSet ==
    \E p \in SlushLoopProcess :
        /\ loopPC[p] = "query"
        /\ loopIter[p] < SlushIterationCount
        /\ \E S \in SUBSET SlushQueryProcess :
             /\ Cardinality(S) = SampleSetSize
             /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
        /\ \E n \in Node :
             /\ <<n, p>> \in HostMapping
             /\ messages' = messages \cup [src |-> p, dst |-> x, kind |-> "query", col |-> color[n] : x \in sampleSet[p]]
        /\ UNCHANGED <<color, loopPC, queryPC, loopIter>>

\* A query process adopts the query's color if uncolored, then replies.
RespondToQuery ==
    \E q \in SlushQueryProcess :
        /\ queryPC[q] = "replyLoop"
        /\ \E p \in SlushLoopProcess :
             /\ <<p, q>> \in HostMapping
             /\ [src |-> p, dst |-> q, kind |-> "query", col |-> NoColor] \in messages
             /\ color' = IF color[CHOOSE n \in Node : <<n, q>> \in HostMapping] = NoColor
                         THEN [color EXCEPT ![CHOOSE n \in Node : <<n, q>> \in HostMapping] = col]
                         ELSE color
             /\ messages' = (messages \ {[src |-> p, dst |-> q, kind |-> "query", col |-> NoColor]})
                            \cup {[src |-> q, dst |-> p, kind |-> "reply", col |-> color[CHOOSE n \in Node : <<n, q>> \in HostMapping]]}
        /\ UNCHANGED <<loopPC, queryPC, sampleSet, loopIter>>

TallyReplies ==
    \E p \in SlushLoopProcess :
        /\ loopPC[p] = "query"
        /\ \A q \in sampleSet[p] : [src |-> q, dst |-> p, kind |-> "reply", col |-> NoColor] \in messages
        /\ \E c \in Node :
             /\ Cardinality({q \in sampleSet[p] : [src |-> q, dst |-> p, kind |-> "reply", col |-> c] \in messages}) >= PickFlipThreshold
             /\ color' = [color EXCEPT ![CHOOSE n \in Node : <<n, p>> \in HostMapping] = c]
        /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
        /\ loopIter' = [loopIter EXCEPT ![p] = loopIter[p] + 1]
        /\ loopPC' = [loopPC EXCEPT ![p] = IF loopIter[p] + 1 = SlushIterationCount THEN "done" ELSE "idle"]
        /\ UNCHANGED <<messages, queryPC>>

LoopTermination ==
    \E p \in SlushLoopProcess :
        /\ loopPC[p] = "done"
        /\ [src |-> p, dst |-> p, kind |-> "done", col |-> NoColor] \notin messages
        /\ messages' = messages \cup {[src |-> p, dst |-> p, kind |-> "done", col |-> NoColor]}
        /\ UNCHANGED <<color, loopPC, queryPC, sampleSet, loopIter>>

QueryLoopExit ==
    \E q \in SlushQueryProcess :
        /\ queryPC[q] = "replyLoop"
        /\ \A p \in SlushLoopProcess : [src |-> p, dst |-> p, kind |-> "done", col |-> NoColor] \in messages
        /\ queryPC' = [queryPC EXCEPT ![q] = "done"]
        /\ UNCHANGED <<color, messages, loopPC, sampleSet, loopIter>>

Next ==
    \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
    /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
    /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

AllProcessesDone ==
    /\ \A p \in SlushLoopProcess : loopPC[p] = "done"
    /\ \A q \in SlushQueryProcess : queryPC[q] = "done"

Termination == <>(AllProcessesDone /\ \A c \in Message : c \in messages)
====