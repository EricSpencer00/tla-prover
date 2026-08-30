---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Message set is the only shared resource; all actors are interlocked through it.
MessageType == [kind: {"query", "reply", "termination"}, from: SlushLoopProcess, to: SlushQueryProcess, color: {NoColor} \union {
  [x \in {NoColor} \union Node: x] / (x = NoColor => NoMessage |-> NoMessage) }]

VARIABLES nodeColor, inbox, pc, loopClient, loopIt

vars == <<nodeColor, inbox, pc, loopClient, loopIt>>

Typed == /\ nodeColor \in [Node -> {NoColor} \union {NoMessage}]
         /\ inbox \subseteq MessageType
         /\ pc \in [SlushLoopProcess -> {"waitColor", "polling", "tallying", "done"}]
         /\ loopClient \in [SlushLoopProcess -> Node]
         /\ loopIt \in [SlushLoopProcess -> 0..SlushIterationCount]

SomeQuery == CHOOSE m \in inbox : m.kind = "query"

Init == /\ nodeColor = [n \in Node |-> NoColor]
        /\ inbox = {}
        /\ pc = [lp \in SlushLoopProcess |-> "waitColor"]
        /\ loopClient = [lp \in SlushLoopProcess |-> CHOOSE n \in Node : <<lp, n>> \in HostMapping]
        /\ loopIt = [lp \in SlushLoopProcess |-> 0]

\* The client role (outside the consensus loop) assigns the first colors.
AssignColor == \E n \in Node, c \in {NoColor} \union {NoMessage} :
                 /\ nodeColor[n] = NoColor
                 /\ c # NoColor
                 /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
                 /\ UNCHANGED <<inbox, pc, loopClient, loopIt>>

RequireColor == \E lp \in SlushLoopProcess :
                  /\ pc[lp] = "waitColor"
                  /\ nodeColor[loopClient[lp]] =/= NoColor
                  /\ pc' = [pc EXCEPT ![lp] = "polling"]
                  /\ UNCHANGED <<nodeColor, inbox, loopClient, loopIt>>

QuerySampleSet == \E lp \in SlushLoopProcess :
                    /\ pc[lp] = "polling"
                    /\ loopIt[lp] < SlushIterationCount
                    /\ \E sample \in [SlushQueryProcess -> BOOLEAN] :
                         /\ Cardinality({q \in SlushQueryProcess : sample[q]}) = SampleSetSize
                         /\ inbox' = inbox \union
                             { [kind |-> "query", from |-> lp, to |-> q,
                                color |-> [x \in {NoColor} \union Node |-> IF x = NoColor THEN NoMessage ELSE nodeColor[x]]] :
                                 q \in SlushQueryProcess /\ sample[q] }
                    /\ pc' = [pc EXCEPT ![lp] = "tallying"]
                    /\ UNCHANGED <<nodeColor, loopClient, loopIt>>

RespondToQuery == \E m \in inbox :
                    /\ m.kind = "query"
                    /\ nodeColor' = [nodeColor EXCEPT ![SomeQuery.to] = IF m.color = NoMessage THEN nodeColor[SomeQuery.to] ELSE m.color]
                    /\ inbox' = (inbox \ {SomeQuery})
                          \union {[kind |-> "reply", from |-> SomeQuery.from, to |-> SomeQuery.to,
                                    color |-> [x \in {NoColor} \union Node |-> IF x = NoColor THEN NoMessage ELSE nodeColor[x]]]}
                    /\ UNCHANGED <<pc, loopClient, loopIt>>

TallyReplies == \E lp \in SlushLoopProcess :
                  /\ pc[lp] = "tallying"
                  /\ \E sample \in [SlushQueryProcess -> BOOLEAN] :
                       \A q \in SlushQueryProcess :
                         (sample[q] => \E m \in inbox : m.kind = "reply" /\ m.from = lp /\ m.to = q)
                  /\ LET votes == {m \in inbox : m.kind = "reply" /\ m.from = lp}
                         yes(c) == Cardinality({m \in votes : m.color[x \in {NoColor} \union Node] = c})
                     IN
                       /\ IF \E c \in {NoColor} \union Node : yes(c) >= PickFlipThreshold
                             THEN nodeColor' = [nodeColor EXCEPT ![loopClient[lp]] = c]
                             ELSE nodeColor' = nodeColor
                       /\ inbox' = inbox \ {m \in inbox : m.kind = "reply" /\ m.from = lp}
                  /\ loopIt' = [loopIt EXCEPT ![lp] = loopIt[lp] + 1]
                  /\ pc' = IF loopIt[lp] + 1 = SlushIterationCount THEN "done" ELSE "polling"

LoopTerminate == \E lp \in SlushLoopProcess :
                    /\ pc[lp] = "done"
                    /\ ~\E m \in inbox : m.kind = "termination" /\ m.from = lp
                    /\ inbox' = inbox \union {[kind |-> "termination", from |-> lp, to |-> SomeQuery.to, color |-> NoMessage]}
                    /\ UNCHANGED <<nodeColor, pc, loopClient, loopIt>>

QueryLoopExit == \A lp \in SlushLoopProcess : pc[lp] = "done" /\ \A m \in inbox : m.kind # "query"

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate)

TypeInvariant == /\ nodeColor \in [Node -> {NoColor} \union {NoMessage}]
                 /\ inbox \subseteq MessageType
                 /\ pc \in [SlushLoopProcess -> {"waitColor", "polling", "tallying", "done"}]
                 /\ loopClient \in [SlushLoopProcess -> Node]
                 /\ loopIt \in [SlushLoopProcess -> 0..SlushIterationCount]

Termination == <>(QueryLoopExit /\ QuerySampleSet)

====