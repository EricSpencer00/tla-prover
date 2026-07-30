---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* MessageSet carries every in-flight message; it is the only shared queue.
\* Protocol actions keep it well-typed; the safety property below only
\* inspects the shape of messages that are already in the set.
Message == [tag: {"query", "reply", "term"}, from: SlushLoopProcess,
            to: SlushQueryProcess, color: NoColor..2]
MessageSet == SUBSET Message

VARIABLES color, inbox, pc, sampleSet, iterations

vars == <<color, inbox, pc, sampleSet, iterations>>

LoopFor == [stage: {"waitColor", "tally", "done"}, phase: 0..2]
QueryFor == [stage: {"reply", "done"}]
RequestFor == [stage: {"ready", "done"}]

TypeOK ==
  /\ color \in [Node -> (NoColor..2)]
  /\ inbox \in MessageSet
  /\ pc \in [SlushLoopProcess -> LoopFor]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess |-> [stage |-> "waitColor", phase |-> 0]]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ \E n \in Node, col \in 1..2 :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<inbox, pc, sampleSet, iterations>>

RequireColor ==
  /\ \E p \in SlushLoopProcess, n \in Node :
       /\ HostMapping[p].node = n
       /\ color[n] # NoColor
       /\ pc[p].stage = "waitColor"
       /\ pc' = [pc EXCEPT ![p].stage = "tally"]
  /\ UNCHANGED <<color, inbox, sampleSet, iterations>>

\* Sample set is chosen only once per iteration, so it stays frozen after
\* the messages are in flight.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess, target \in SlushQueryProcess :
       /\ pc[p].stage = "tally"
       /\ pc[p].phase = 0
       /\ target # HostMapping[p].query
       /\ Cardinality(sampleSet[p]) < SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![p] = @ \cup {target}]
       /\ inbox' = inbox \cup {[tag |-> "query", from |-> p,
                                to |-> target, color |-> color[HostMapping[p].node]]}
       /\ UNCHANGED <<color, pc, iterations>>

\* A query process adopts the query's color only if it is still uncolored.
RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.tag = "query"
       /\ m.to \in SlushQueryProcess
       /\ color' = [color EXCEPT ![HostMapping[m.to].node] =
                       IF color[HostMapping[m.to].node] = NoColor
                       THEN m.color ELSE color[HostMapping[m.to].node]]
       /\ inbox' = (inbox \ {m}) \cup
                     {[tag |-> "reply", from |-> m.from,
                        to |-> m.to, color |-> color[HostMapping[m.to].node]]}
       /\ UNCHANGED <<pc, sampleSet, iterations>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess, n \in Node :
       /\ pc[p].stage = "tally"
       /\ pc[p].phase = 0
       /\ \A q \in sampleSet[p] :
            \E m \in inbox :
              /\ m.tag = "reply"
              /\ m.from = p
              /\ m.to = q
              /\ m.color = color[n]
              /\ inbox' = inbox \ {m}
       /\ LET tally(c) == Cardinality({q \in sampleSet[p] :
                 \E m \in inbox : m.tag = "reply" /\ m.from = p /\ m.to = q /\ m.color = c})
          IN color' = [color EXCEPT ![n] =
               IF tally(1) >= PickFlipThreshold THEN 1
               ELSE IF tally(2) >= PickFlipThreshold THEN 2 ELSE @]
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
       /\ pc' = [pc EXCEPT ![p].phase = 1]

BroadcastTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p].stage = "tally"
       /\ pc[p].phase = 1
       /\ iterations[p] = SlushIterationCount
       /\ inbox' = inbox \cup {[tag |-> "term", from |-> p, to |-> NoMessage,
                                color |-> NoColor]}
       /\ pc' = [pc EXCEPT ![p].stage = "done"]
  /\ UNCHANGED <<color, sampleSet, iterations>>

\* Query processes leave once every loop process has terminated.
QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ \A p \in SlushLoopProcess : pc[p].stage = "done"
       /\ pc' = [pc EXCEPT ![HostMapping[q].loop].stage = "done"]
  /\ UNCHANGED <<color, inbox, sampleSet, iterations>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ BroadcastTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies) /\ WF_vars(BroadcastTerminate) /\ WF_vars(QueryLoopExit)

AllProcessesDone == \A p \in SlushLoopProcess : pc[p].stage = "done"

Properties == AllProcessesDone

====