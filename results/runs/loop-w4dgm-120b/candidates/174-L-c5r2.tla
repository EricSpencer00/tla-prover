---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest member of the Snow family (Team Rocket, 2018).
\* It has no quorum leader; nodes sample peers and adopt a popular color.
\* This spec is written in PlusCal and models the message flow as sets
\* of messages rather than a channel with ordering, because TLA+ has no
\* probabilistic or ordering primitive here.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Process roles for the two flavours of Slush process, tied back to the
\* node they host on through HostMapping.
Roles == {"loop", "query"}

VARIABLES
  color,        \* node -> color (or NoColor) : each node's current opinion
  messages,     \* set of in-flight messages (query, reply, termination)
  pc,           \* process -> role ("loop" or "query") + step: where it is
  sampleSet,    \* loop process -> set of query-process peers it sampled this round
  loopIters     \* loop process -> iterations it has completed

vars == <<color, messages, pc, sampleSet, loopIters>>

LoopProcesses == HostMapping[SlushLoopProcess]
QueryProcesses == HostMapping[SlushQueryProcess]

MessageDomain == {"src", "dst", "kind", "payload"}

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in LoopProcesses \cup QueryProcesses |-> [role |-> "query", step |-> "replying"]]
  /\ sampleSet = [lp \in LoopProcesses |-> {}]
  /\ loopIters = [lp \in LoopProcesses |-> 0]

ClientAssignColor(n, col) ==
  /\ color[n] = NoColor
  /\ col # NoColor
  /\ color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<messages, pc, sampleSet, loopIters>>

RequireHostColor(p) ==
  /\ pc[p].role = "loop"
  /\ pc[p].step = "wait"
  /\ color[HostMapping[p]] # NoColor
  /\ pc' = [pc EXCEPT ![p] = [@ EXCEPT !.step = "idle"]]
  /\ UNCHANGED <<color, messages, sampleSet, loopIters>>

\* The loop process samples a fixed-size peer set and queries their colors.
QuerySampleSet(p) ==
  /\ pc[p].role = "loop"
  /\ pc[p].step = "idle"
  /\ Cardinality(sampleSet[p]) < SampleSetSize
  /\ \E q \in QueryProcesses :
       /\ q \notin sampleSet[p]
       /\ sampleSet' = [sampleSet EXCEPT ![p] = @ \cup {q}]
       /\ messages' = messages \cup {[src |-> p, dst |-> q, kind |-> "query", payload |-> color[HostMapping[p]]]}
  /\ UNCHANGED <<color, pc, loopIters>>

RespondToQuery(q, src, col) ==
  /\ [src |-> src, dst |-> q, kind |-> "query", payload |-> col] \in messages
  /\ messages' = messages \ {[src |-> src, dst |-> q, kind |-> "query", payload |-> col]}
  /\ \E adjCol \in {color[HostMapping[q]], col} :
       color' = [color EXCEPT ![HostMapping[q]] = adjCol]
  /\ messages' = messages \cup {[src |-> q, dst |-> src, kind |-> "reply", payload |-> color[HostMapping[q]]]}
  /\ UNCHANGED <<pc, sampleSet, loopIters>>

\* The loop counts replies; once a color meets the flip threshold it adopts it.
TallyReplies(p) ==
  /\ pc[p].role = "loop"
  /\ Cardinality(sampleSet[p]) >= SampleSetSize
  /\ \A q \in sampleSet[p] : [src |-> q, dst |-> p, kind |-> "reply", payload |-> "x"] \in messages
  /\ \E col \in {1, 2} :
       /\ 2 * Cardinality({q \in sampleSet[p] : [src |-> q, dst |-> p, kind |-> "reply", payload |-> col] \in messages})
            >= PickFlipThreshold
       /\ color' = [color EXCEPT ![HostMapping[p]] = col]
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ loopIters' = [loopIters EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<messages, pc>>

LoopTermination(p) ==
  /\ pc[p].role = "loop"
  /\ loopIters[p] = SlushIterationCount
  /\ pc[p].step # "done"
  /\ pc' = [pc EXCEPT ![p] = [@ EXCEPT !.step = "done"]]
  /\ messages' = messages \cup {[src |-> p, dst |-> NoMessage, kind |-> "terminate", payload |-> NoMessage]}
  /\ UNCHANGED <<color, sampleSet, loopIters>>

QueryLoopExit(q) ==
  /\ pc[q].role = "query"
  /\ pc[q].step = "replying"
  /\ \A p \in LoopProcesses : [src |-> p, dst |-> NoMessage, kind |-> "terminate", payload |-> NoMessage] \in messages
  /\ pc' = [pc EXCEPT ![q] = [@ EXCEPT !.step = "done"]]
  /\ UNCHANGED <<color, messages, sampleSet, loopIters>>

Next ==
  \/ \E n \in Node, col \in {1, 2} : ClientAssignColor(n, col)
  \/ \E p \in LoopProcesses : RequireHostColor(p)
  \/ \E p \in LoopProcesses : QuerySampleSet(p)
  \/ \E q \in QueryProcesses, src \in LoopProcesses, col \in {1, 2} : RespondToQuery(q, src, col)
  \/ \E p \in LoopProcesses : TallyReplies(p)
  \/ \E p \in LoopProcesses : LoopTermination(p)
  \/ \E q \in QueryProcesses : QueryLoopExit(q)

Spec == Init /\ [][Next]_vars /\ (\A p \in LoopProcesses : WF_vars(LoopTermination(p)))

\* Runtime safety: no process is stuck on a message that never arrives.
TypeInvariant ==
  /\ messages \subseteq [MessageDomain -> SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} \cup {1, 2, NoColor}]
  /\ color \in [Node -> {1, 2} \cup {NoColor}]

Termination == \A p \in LoopProcesses \cup QueryProcesses : pc[p].step = "done"

====