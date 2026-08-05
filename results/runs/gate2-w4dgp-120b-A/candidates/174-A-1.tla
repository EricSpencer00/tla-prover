---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* This module implements the Slush protocol from the Avalanche whitepaper in
\* PlusCal.  Because PlusCal / TLA+ has no native probabilistic primitives,
\* the actual convergence of the network is treated as an external
\* correctness argument; the model here focuses on the control flow, message
\* types, and termination of every participant (loop processes, query
\* processes, and the client request process).
CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME HostMapping = [lp \in SlushLoopProcess |-> q \in SlushQueryProcess, n \in Node]
  /\ Cardinality(SlushLoopProcess) = Cardinality(SlushQueryProcess)
  /\ Cardinality(SlushLoopProcess) = Cardinality(Node)

\* Messages flow between the loop processes and the query processes.  A
\* query process only ever needs to know its host's current color, so the
\* network model is a simple unordered pool rather than a FIFO queue.
Message == [from : SlushLoopProcess, to : SlushQueryProcess, kind : {"query"}, color : {NoColor} \union Node] \union [from : SlushQueryProcess, to : SlushLoopProcess, kind : {"queryReply"}, color : Node]
          \union [from : SlushLoopProcess, to : "client", kind : {"termination"}]

VARIABLES color, inbox, pc, sample, loopIter

TypeOK ==
  /\ color \in [Node -> {NoColor} \union Node]
  /\ inbox \subseteq Message
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"client"} -> 0..3]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"client"} |-> IF p = "client" THEN 0 ELSE 1]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ loopIter = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ pc["client"] = 0
  /\ \E n \in Node : color[n] = NoColor /\ \E c \in Node : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 1]
  /\ UNCHANGED <<inbox, sample, loopIter>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 1
       /\ color[HostMapping[lp].n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = 2]
  /\ UNCHANGED <<color, inbox, sample, loopIter>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ Cardinality(sample[lp]) < SampleSetSize
       /\ \E q \in SlushQueryProcess : q # HostMapping[lp] /\ q \notin sample[lp]
            /\ inbox' = inbox \union {[from |-> lp, to |-> q, kind |-> "query", color |-> color[HostMapping[lp].n]]}
            /\ sample' = [sample EXCEPT ![lp] = @ \union {q}]
  /\ UNCHANGED <<color, pc, loopIter>>

RespondToQuery ==
  /\ \E m \in inbox :
       /\ m.kind = "query"
       /\ \E c \in Node : color' = [color EXCEPT ![HostMapping[m.to].n] = IF color[HostMapping[m.to].n] = NoColor THEN m.color ELSE color[HostMapping[m.to].n]]
       /\ inbox' = (inbox \ {m}) \union {[from |-> m.to, to |-> m.from, kind |-> "queryReply", color |-> HostMapping[m.to].n]}
  /\ UNCHANGED <<pc, sample, loopIter>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = 2
       /\ \A m \in inbox : m.kind = "query" => m.from = lp
       /\ Cardinality(sample[lp]) = SampleSetSize
       /\ \E c \in Node :
            /\ Cardinality({m \in inbox : m.kind = "queryReply" /\ m.to = lp /\ m.color = c}) >= PickFlipThreshold
            /\ color' = [color EXCEPT ![HostMapping[lp].n] = c]
       /\ inbox' = {m \in inbox : m.kind # "queryReply" /\ m.to # lp}
       /\ sample' = [sample EXCEPT ![lp] = {}]
       /\ loopIter' = [loopIter EXCEPT ![lp] = IF @ >= SlushIterationCount THEN @ ELSE @ + 1]
       /\ pc' = [pc EXCEPT ![lp] = IF loopIter[lp] >= SlushIterationCount THEN 2 ELSE 1]
  /\ UNCHANGED <<pc>>

LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ loopIter[lp] >= SlushIterationCount
       /\ pc[lp] = 2
       /\ inbox' = inbox \union {[from |-> lp, to |-> "client", kind |-> "termination"]}
       /\ pc' = [pc EXCEPT ![lp] = 3]
  /\ UNCHANGED <<color, sample, loopIter>>

QueryLoopExit ==
  /\ (\A lp \in SlushLoopProcess : pc[lp] = 3) => \A q \in SlushQueryProcess : pc[q] = 3
  /\ UNCHANGED <<color, inbox, pc, sample, loopIter>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_<<color, inbox, pc, sample, loopIter>>

ProcessTermination == <>(\A p \in SlushLoopProcess \union SlushQueryProcess \union {"client"} : pc[p] = 3)

====