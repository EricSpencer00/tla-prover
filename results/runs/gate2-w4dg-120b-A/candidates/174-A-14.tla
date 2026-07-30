---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* Loop processes drive the Slush iteration; query processes reply to
\* sampled queries; the client process assigns the first colors.
\* Colors: two actual colors plus the uncolored sentinel.
Colors == {0, 1, NoColor}

\* message format: a quadruple tagging the send direction (query,
\* reply, termination) plus the three registered IDs.
Message == [kind : {"query", "reply", "terminate"},
            loop : SlushLoopProcess,
            query : SlushQueryProcess,
            color : Colors]

\*  loopProc/hostProcess are each the inverse of HostMapping on one side.
LoopOf(n) == CHOOSE l \in SlushLoopProcess : HostMapping[l].node = n
QueryOf(n) == CHOOSE q \in SlushQueryProcess : HostMapping[q].node = n

VARIABLES color, messages, pc, sample, loopsDone

vars == <<color, messages, pc, sample, loopsDone>>

TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ messages \subseteq Message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..3]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ loopsDone = [l \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (one transaction).
ClientAssignColor ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ \E c \in {0, 1} : color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT !["client"] = 1]
    /\ UNCHANGED <<messages, sample, loopsDone>>

RequireColor ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 0
         /\ LoopOf(l) \in {n \in Node : color[n] # NoColor}
         /\ pc' = [pc EXCEPT ![l] = 1]
    /\ UNCHANGED <<color, messages, sample, loopsDone>>

\* The loop process samples a fixed-size set of other nodes' query procs.
QuerySampleSet ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 1
         /\ loopsDone[l] < SlushIterationCount
         /\ \E Q \in SUBSET (SlushQueryProcess \ {QueryOf(LoopOf(l))}) :
              Cardinality(Q) = SampleSetSize
              /\ sample' = [sample EXCEPT ![l] = Q]
         /\ messages' = messages \cup
              {[kind |-> "query", loop |-> l, query |-> q, color |-> color[LoopOf(l)]]
                  : q \in sample[l]}
         /\ pc' = [pc EXCEPT ![l] = 2]
    /\ UNCHANGED <<color, loopsDone>>

\* A query process answers with its own current color (adopting the
\* query's color first if it is still uncolored).
RespondToQuery ==
    /\ \E msg \in messages :
         /\ msg.kind = "query"
         /\ color[HostMapping[msg.query].node] = NoColor
         /\ color' = [color EXCEPT ![HostMapping[msg.query].node] = msg.color]
         /\ messages' = (messages \ {msg}) \cup
              {[kind |-> "reply", loop |-> msg.loop, query |-> msg.query,
                 color |-> IF color[HostMapping[msg.query].node] = NoColor
                            THEN msg.color
                            ELSE color[HostMapping[msg.query].node]]}
    /\ UNCHANGED <<pc, sample, loopsDone>>

TallyReplies ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 2
         /\ Cardinality(sample[l]) = SampleSetSize
         /\ Cardinality({msg \in messages : msg.kind = "reply" /\ msg.loop = l})
              = SampleSetSize
         /\ (\E c \in {0, 1} :
               Cardinality({msg \in messages : msg.kind = "reply" /\ msg.loop = l
                            /\ msg.color = c}) >= PickFlipThreshold
                  /\ color' = [color EXCEPT ![LoopOf(l)] = c])
         /\ messages' = messages \ {msg \in messages : msg.kind = "reply" /\ msg.loop = l}
         /\ sample' = [sample EXCEPT ![l] = {}]
         /\ loopsDone' = [loopsDone EXCEPT ![l] = @ + 1]
         /\ pc' = [pc EXCEPT ![l] = 3]
    /\ UNCHANGED <<>>

LoopTermination ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 3
         /\ loopsDone[l] = SlushIterationCount
         /\ messages' = messages \cup
              {[kind |-> "terminate", loop |-> l, query |-> QueryOf(LoopOf(l)), color |-> NoColor]}
         /\ pc' = [pc EXCEPT ![l] = 4]
    /\ UNCHANGED <<color, sample, loopsDone>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
         /\ pc[q] = 0
         /\ \A m \in messages : m.kind = "terminate"
         /\ pc' = [pc EXCEPT ![q] = 4]
    /\ UNCHANGED <<color, messages, sample, loopsDone>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(TallyReplies) /\ WF_vars(QueryLoopExit)

\* All processes eventually reach a done state.
Termination == <>(\A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pc[p] = 4)

====