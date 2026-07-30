---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

Process == SlushLoopProcess \cup SlushQueryProcess

\* Each node has a loop process that samples peers and a query process that
\* responds. The host mapping (node, loop, query) links them.
\* SlushIterationCount bounds how many rounds a loop process may run.
\* SampleSetSize is the number of peers queried per round; PickFlipThreshold
\* is the quorum a color must reach to be adopted.
\* NoColor / NoMessage are sentinel values used throughout the spec.

Message == [kind : {"query", "queryReply", "done"}, from : Process, to : Process, col : {NoColor} \cup {"blue", "green"}]

VARIABLES
  color, msgs, loopPc, queryPc, sample, loopIter

vars == <<color, msgs, loopPc, queryPc, sample, loopIter>>

TypeOK ==
  /\ color \in [Node -> {NoColor, "blue", "green"}]
  /\ msgs \subseteq Message
  /\ loopPc \in [SlushLoopProcess -> {"waitingForColor", "sampling", "waitingForReplies", "done"}]
  /\ queryPc \in [SlushQueryProcess -> {"handling", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ loopPc = [p \in SlushLoopProcess |-> "waitingForColor"]
  /\ queryPc = [q \in SlushQueryProcess |-> "handling"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node.
\* This is what seeds the network before any loop process acts.
ClientAssignColor ==
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in {"blue", "green"} : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, loopPc, queryPc, sample, loopIter>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ loopPc[p] = "waitingForColor"
       /\ \E n \in Node :
            /\ <<n, p, Head({q \in SlushQueryProcess : \E m \in HostMapping : m[1] = p /\ m[2] = q})>> \in HostMapping
            /\ color[n] # NoColor
            /\ loopPc' = [loopPc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<color, msgs, queryPc, sample, loopIter>>

\* A loop process samples a random (nondeterministic) peer set of fixed size.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ loopPc[p] = "sampling"
       /\ loopIter[p] < SlushIterationCount
       /\ \E S \in SUBSET SlushQueryProcess :
            /\ Cardinality(S) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = S]
            /\ msgs' = msgs \cup {[kind |-> "query", from |-> p, to |-> q, col |-> color[Head({n \in Node : \E m \in HostMapping : m[1] = p /\ m[2] = n})]] : q \in S}
       /\ loopPc' = [loopPc EXCEPT ![p] = "waitingForReplies"]
  /\ UNCHANGED <<color, queryPc, loopIter>>

\* A query process adopts the query's color if it is still uncolored,
\* then replies with its (new) current color.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.kind = "query"
       /\ \E n \in Node :
            /\ <<n, m.from, m.to>> \in HostMapping
            /\ color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.col] ELSE color
            /\ msgs' = (msgs \ {m}) \cup {[kind |-> "queryReply", from |-> m.to, to |-> m.from, col |-> (IF color[n] = NoColor THEN m.col ELSE color[n])]}
  /\ UNCHANGED <<loopPc, queryPc, sample, loopIter>>

\* The loop process waits for every sampled peer to reply, then adopts
\* any color that reached the flip threshold. One round is consumed.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ loopPc[p] = "waitingForReplies"
       /\ \E S \in SUBSET Message :
            /\ S = {m \in msgs : m.kind = "queryReply" /\ m.to = p /\ m.from \in sample[p]}
            /\ Cardinality(S) = SampleSetSize
            /\ LET blue == Cardinality({m \in S : m.col = "blue"})
               green == Cardinality({m \in S : m.col = "green"}) IN
                 color' = IF blue >= PickFlipThreshold THEN [color EXCEPT ![Head({n \in Node : \E m \in HostMapping : m[1] = p /\ m[2] = n})] = "blue"]
                          ELSE IF green >= PickFlipThreshold THEN [color EXCEPT ![Head({n \in Node : \E m \in HostMapping : m[1] = p /\ m[2] = n})] = "green"]
                          ELSE color
            /\ msgs' = msgs \ S
            /\ loopPc' = [loopPc EXCEPT ![p] = "sampling"]
            /\ loopIter' = [loopIter EXCEPT ![p] = loopIter[p] + 1]
            /\ sample' = [sample EXCEPT ![p] = {}]
  /\ UNCHANGED queryPc

\* After using its allocated iterations a loop process signals termination.
LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ loopPc[p] = "sampling"
       /\ loopIter[p] = SlushIterationCount
       /\ loopPc' = [loopPc EXCEPT ![p] = "done"]
       /\ msgs' = msgs \cup {[kind |-> "done", from |-> p, to |-> p, col |-> NoColor]}
  /\ UNCHANGED <<color, queryPc, sample, loopIter>>

\* A query process halts once every loop process has sent its done message.
QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ queryPc[q] = "handling"
       /\ \A p \in SlushLoopProcess : loopPc[p] = "done"
       /\ queryPc' = [queryPc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgs, loopPc, sample, loopIter>>

Next ==
  \/ ClientAssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(ClientAssignColor) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

TypeInvariant == TypeOK

AllProcessesEventuallyDone ==
  /\ \A p \in SlushLoopProcess : <>(loopPc[p] = "done")
  /\ \A q \in SlushQueryProcess : <>(queryPc[q] = "done")

====