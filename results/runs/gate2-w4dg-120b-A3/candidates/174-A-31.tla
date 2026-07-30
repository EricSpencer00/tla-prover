---- MODULE Slush ----
EXTENDS Naturals, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Types of messages on Slush's wire (None is the empty element for the message set,
\* used so PlusCal's Init/Next can be total even when nothing is ready).
MessageType == {"query", "queryReply", "termination"}
QueryMessage == [kind : "query", from : SlushLoopProcess, to : SlushQueryProcess, payload : {0, 1, NoColor}]
ReplyMessage == [kind : "queryReply", from : SlushQueryProcess, to : SlushLoopProcess, payload : {0, 1, NoColor}]
TerminationMessage == [kind : "termination", from : SlushLoopProcess]

VARIABLES assignColor, messages, pc, sampleSet, loopIter

vars == <<assignColor, messages, pc, sampleSet, loopIter>>

\* Link a node to its loop and query processes; each node has exactly one of each.
ProcOf(n) == CHOOSE p \in HostMapping : p[1] = n
QueryProcOf(n) == CHOOSE p \in HostMapping : p[2] = n

TypeOK ==
  /\ assignColor \in [Node -> {0, 1, NoColor}]
  /\ messages \subseteq (QueryMessage \cup ReplyMessage \cup TerminationMessage)
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"waitingColor", "sampling", "replying", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "waitingColor"]
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ loopIter = [l \in SlushLoopProcess |-> 0]

\* An external client process assigns an initial color to an uncolored node.
ClientAssign ==
  /\ pc["client"] = "waitingColor"
  /\ \E n \in Node :
       /\ assignColor[n] = NoColor
       /\ \E c \in {0, 1} : assignColor' = [assignColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "waitingColor"]
  /\ UNCHANGED <<messages, sampleSet, loopIter>>

RequireColor ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "waitingColor"
       /\ assignColor[QueryProcOf(l)] # NoColor
       /\ pc' = [pc EXCEPT ![l] = "sampling"]
  /\ UNCHANGED <<assignColor, messages, sampleSet, loopIter>>

QuerySampleSet ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "sampling"
       /\ loopIter[l] < SlushIterationCount
       /\ \E subset \in SUBSET SlushQueryProcess :
            /\ Cardinality(subset) = SampleSetSize
            /\ \A q \in subset : q # QueryProcOf(l)
            /\ sampleSet' = [sampleSet EXCEPT ![l] = subset]
            /\ messages' = messages \cup {[kind |-> "query", from |-> l, to |-> q, payload |-> assignColor[QueryProcOf(l)]] : q \in subset}
  /\ UNCHANGED <<assignColor, pc, loopIter>>

RespondToQuery ==
  /\ \E m \in messages :
       /\ m.kind = "query"
       /\ assignColor' = [assignColor EXCEPT ![QueryProcOf(m.to)] =
                            IF assignColor[QueryProcOf(m.to)] = NoColor THEN m.payload ELSE assignColor[QueryProcOf(m.to)]]
       /\ messages' = (messages \ {m}) \cup {[kind |-> "queryReply", from |-> m.to, to |-> m.from, payload |-> assignColor[QueryProcOf(m.to)]]}
  /\ UNCHANGED <<pc, sampleSet, loopIter>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "sampling"
       /\ sampleSet[l] # {}
       /\ \A q \in sampleSet[l] : \E m \in messages : m.kind = "queryReply" /\ m.from = q /\ m.to = l
       /\ LET replies == {m.payload : m \in messages : m.kind = "queryReply" /\ m.to = l}
          count(c) == Cardinality({w \in replies : w = c})
          newColor == IF count(0) >= PickFlipThreshold THEN 0
                       ELSE IF count(1) >= PickFlipThreshold THEN 1
                       ELSE assignColor[QueryProcOf(l)]
       IN /\ assignColor' = [assignColor EXCEPT ![QueryProcOf(l)] = newColor]
          /\ pc' = [pc EXCEPT ![l] = "replying"]
          /\ messages' = {m \in messages : ~(m.kind = "queryReply" /\ m.to = l)}
          /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
  /\ UNCHANGED loopIter

LoopBack ==
  /\ \E l \in SlushLoopProcess :
       /\ pc[l] = "replying"
       /\ loopIter' = [loopIter EXCEPT ![l] = @ + 1]
       /\ pc' = [pc EXCEPT ![l] = IF @ + 1 = SlushIterationCount THEN "done" ELSE "sampling"]
       /\ messages' = IF @ + 1 = SlushIterationCount
                        THEN messages \cup {[kind |-> "termination", from |-> l]}
                        ELSE messages
  /\ UNCHANGED <<assignColor, sampleSet>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "waitingColor"
       /\ \A l \in SlushLoopProcess : [kind |-> "termination", from |-> l] \in messages
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<assignColor, messages, sampleSet, loopIter>>

Quiesce ==
  /\ \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done"
  /\ UNCHANGED vars

Next == ClientAssign \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopBack \/ QueryLoopExit \/ Quiesce

Spec == Init /\ [][Next]_vars

\* The spec has no way to express "eventually everyone holds the same color".
SlushConverged == FALSE

====