---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

MessageType == {"query", "queryReply", "termination"}

VARIABLES color, msgs, pc, sample, loopIter

vars == <<color, msgs, pc, sample, loopIter>>

\* Process-local PC values: loop processes start by waiting for an
\* initial color assignment.
PcValues == {"waitColor", "samplePeers", "tallyReplies", "doneLoop"}

Message ==
  [kind: MessageType, src: SlushLoopProcess, dst: SlushQueryProcess, col: {NoColor} \cup {0, 1}]

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \cup {0, 1}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess -> PcValues]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess |-> "waitColor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]

ClientAssignColor(n) ==
  /\ color[n] = NoColor
  /\ \E col \in {0, 1} : color' = [color EXCEPT ![n] = col]
  /\ UNCHANGED <<msgs, pc, sample, loopIter>>

LoopStart(p) ==
  /\ pc[p] = "waitColor"
  /\ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "samplePeers"]
  /\ UNCHANGED <<color, msgs, sample, loopIter>>

QuerySampleSet(p) ==
  /\ pc[p] = "samplePeers"
  /\ \E subset \in (SUBSET SlushQueryProcess) :
       /\ subset # {}
       /\ Cardinality(subset) = SampleSetSize
       /\ sample' = [sample EXCEPT ![p] = subset]
  /\ LET srcNode == CHOOSE n \in Node : <<p, n>> \in HostMapping IN
       msgs' = msgs \union
         {[kind |-> "query", src |-> p, dst |-> d,
           col |-> color[srcNode]] : d \in sample[p]}
  /\ UNCHANGED <<color, pc, loopIter>>

\* A query process adopts the query color if it is still uncolored.
RespondToQuery(p, q) ==
  /\ [kind |-> "query", src |-> p, dst |-> q, col |-> "any"] \in msgs
  /\ msgs' = (msgs \ {[kind |-> "query", src |-> p, dst |-> q, col |-> "any"]})
       \union
         CASE color[CHOOSE n \in Node : <<q, n>> \in HostMapping] = NoColor ->
           [kind |-> "queryReply", src |-> q, dst |-> p,
            col |-> color'[[CHOOSE n \in Node : <<q, n>> \in HostMapping] |-> [p]])
         OTHER ->
           [kind |-> "queryReply", src |-> q, dst |-> p,
            col |-> color[CHOOSE n \in Node : <<q, n>> \in HostMapping]]
  /\ UNCHANGED <<color, pc, sample, loopIter>>

TallyReplies(p) ==
  /\ pc[p] = "samplePeers"
  /\ \A q \in sample[p] : [kind |-> "queryReply", src |-> q, dst |-> p, col |-> "any"] \in msgs
  /\ \E cnt0 \in 0..SampleSetSize, cnt1 \in 0..SampleSetSize :
       /\ cnt0 + cnt1 = SampleSetSize
       /\ Cardinality({q \in sample[p] :
            [kind |-> "queryReply", src |-> q, dst |-> p, col |-> 0] \in msgs}) = cnt0
       /\ Cardinality({q \in sample[p] :
            [kind |-> "queryReply", src |-> q, dst |-> p, col |-> 1] \in msgs}) = cnt1
       /\ color' = CASE cnt0 >= PickFlipThreshold -> [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = 0]
                    cnt1 >= PickFlipThreshold -> [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = 1]
                    OTHER -> color
       /\ msgs' = msgs \ {[kind |-> "queryReply", src |-> q, dst |-> p, col |-> "any"] : q \in sample[p]}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ loopIter' = [loopIter EXCEPT ![p] = IF loopIter[p] < SlushIterationCount THEN loopIter[p] + 1 ELSE loopIter[p]]
  /\ pc' = [pc EXCEPT ![p] = IF loopIter[p] < SlushIterationCount THEN "samplePeers" ELSE "doneLoop"]

LoopTerminate(p) ==
  /\ pc[p] = "doneLoop"
  /\ [kind |-> "termination", src |-> p, dst |-> "none", col |-> "none"] \notin msgs
  /\ msgs' = msgs \union {[kind |-> "termination", src |-> p, dst |-> "none", col |-> "none"]}
  /\ UNCHANGED <<color, pc, sample, loopIter>>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess : \E p \in SlushLoopProcess : [kind |-> "termination", src |-> p, dst |-> "none", col |-> "none"] \in msgs
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : ClientAssignColor(n)
  \/ \E p \in SlushLoopProcess : LoopStart(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ \E p \in SlushLoopProcess, q \in SlushQueryProcess : RespondToQuery(p, q)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

Liveness == <>(\A q \in SlushQueryProcess : TRUE)

====