---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A loop process samples peers by sending query messages to their query processes.
\* Loop processes are the only writers of the shared color assignment; query processes
\* simply report their node's current color (or adopt an uncolored node's first query).
\* Slush converges purely through the majority-flip rule near the end of the spec.

Message == [src: SlushLoopProcess, dst: SlushQueryProcess, kind: {"query", "reply", "term"}, payload: {NoColor} \union {"red", "blue"}]

VARIABLES color, inbox, loopPC, loopSamples, loopIters

vars == <<color, inbox, loopPC, loopSamples, loopIters>>

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ loopPC = [l \in SlushLoopProcess |-> "waiting"]
  /\ loopSamples = [l \in SlushLoopProcess |-> {}]
  /\ loopIters = [l \in SlushLoopProcess |-> 0]

Host(l) == CHOOSE m \in HostMapping : m[1] = l
HostNode(l) == Host(l)[2]
HostQuery(m) == CHOOSE q \in SlushQueryProcess : <<m[1], m[2], q>> \in HostMapping

AssignColor ==
  \E n \in Node, c \in {"red", "blue"} :
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<inbox, loopPC, loopSamples, loopIters>>

RequireColor ==
  \E l \in SlushLoopProcess :
    /\ loopPC[l] = "waiting"
    /\ color[HostNode(l)] # NoColor
    /\ loopPC' = [loopPC EXCEPT ![l] = "ready"]
    /\ UNCHANGED <<color, inbox, loopSamples, loopIters>>

QuerySampleSet ==
  \E l \in SlushLoopProcess :
    /\ loopPC[l] = "ready"
    /\ loopSamples[l] = {}
    /\ \E peers \in SUBSET SlushQueryProcess :
         /\ Cardinality(peers) = SampleSetSize
         /\ loopSamples' = [loopSamples EXCEPT ![l] = peers]
         /\ inbox' = inbox \union
              {[src |-> l, dst |-> q, kind |-> "query", payload |-> color[HostNode(l)]] : q \in peers}
    /\ UNCHANGED <<color, loopPC, loopIters>>

RespondQuery ==
  \E m \in inbox :
    /\ m.kind = "query"
    /\ LET newColor == IF color[HostNode(Host(m.dst))] = NoColor THEN m.payload ELSE color[HostNode(Host(m.dst))]
         inbox' == (inbox \ {m}) \union
               {[src |-> m.dst, dst |-> m.src, kind |-> "reply", payload |-> newColor]}
    IN /\ color' = [color EXCEPT ![HostNode(Host(m.dst))] = newColor]
       /\ UNCHANGED <<loopPC, loopSamples, loopIters>>

TallyReplies ==
  \E l \in SlushLoopProcess :
    /\ loopSamples[l] # {}
    /\ \A q \in loopSamples[l] : \E m \in inbox : m.kind = "reply" /\ m.dst = l /\ m.src = q
    /\ \E reds, blues \in 0..SampleSetSize :
         /\ reds + blues = Cardinality(loopSamples[l])
         /\ reds >= PickFlipThreshold => color' = [color EXCEPT ![HostNode(l)] = "red"]
         /\ blues >= PickFlipThreshold => color' = [color EXCEPT ![HostNode(l)] = "blue"]
         /\ \A q \in loopSamples[l] :
              \E m \in inbox : m.kind = "reply" /\ m.dst = l /\ m.src = q /\ m.payload = "red" => reds = reds
       /\ loopSamples' = [loopSamples EXCEPT ![l] = {}]
       /\ loopIters' = [loopIters EXCEPT ![l] = IF loopIters[l] < SlushIterationCount THEN @ + 1 ELSE @]
       /\ UNCHANGED <<loopPC, inbox>>

LoopTerminate ==
  \E l \in SlushLoopProcess :
    /\ loopPC[l] \in {"ready", "done"}
    /\ loopIters[l] = SlushIterationCount
    /\ loopPC[l] # "done"
    /\ loopPC' = [loopPC EXCEPT ![l] = "done"]
    /\ inbox' = inbox \union {[src |-> l, dst |-> NoMessage, kind |-> "term", payload |-> NoColor]}
    /\ UNCHANGED <<color, loopSamples, loopIters>>

QueryLoopExit ==
  \E q \in SlushQueryProcess :
    /\ \A l \in SlushLoopProcess : loopPC[l] = "done"
    /\ loopPC' = [l \in SlushLoopProcess |-> "done"]
    /\ UNCHANGED <<color, inbox, loopSamples, loopIters>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondQuery)
  /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit

TypeInvariant ==
  /\ color \in [Node -> {NoColor, "red", "blue"}]
  /\ inbox \subseteq Message
  /\ loopPC \in [SlushLoopProcess -> {"waiting", "ready", "done"}]
  /\ loopSamples \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIters \in [SlushLoopProcess -> 0..SlushIterationCount]

Terminating == \A l \in SlushLoopProcess : loopPC[l] = "done"

EventuallyTerminating == <>(Terminating)
====