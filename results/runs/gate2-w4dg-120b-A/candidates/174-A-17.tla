---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Loop processes drive Slush's metastable consensus by sampling peers and
\* adopting a sufficiently popular color. Query processes simply return the
\* current color of their host node (adopting a query's color if uncolored),
\* and the client request process initially colors uncolored nodes.

VARIABLES
  color, msgSet, pc, sample, loopIters

vars == <<color, msgSet, pc, sample, loopIters>>

Message == [kind: {"query", "reply", "term"}, src: SlushLoopProcess, dst: SlushQueryProcess, qcolor: 0..2]
QueryKind == [kind: "query", src: SlushLoopProcess, dst: SlushQueryProcess, qcolor: 0..1]
ReplyKind == [kind: "reply", src: SlushLoopProcess, dst: SlushQueryProcess, qcolor: 0..1]
TermKind == [kind: "term", src: SlushLoopProcess, dst: SlushQueryProcess, qcolor: 0]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgSet = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushLoopProcess THEN "waitColor" ELSE "replyLoop"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIters = [p \in SlushLoopProcess |-> 0]

\* Client assigns an initial random color to an uncolored node.
RequestAssignColor ==
  /\ \E n \in Node, c \in 0..1 : color[n] = NoColor /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgSet, pc, sample, loopIters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waitColor"
       /\ \E n \in Node : HostMapping[n].loop = p /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "sample"]
  /\ UNCHANGED <<color, msgSet, sample, loopIters>>

\* Loop process queries a random subset of other nodes' query processes.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sample"
       /\ \E peers \in SUBSET SlushQueryProcess :
            /\ peers # {}
            /\ Cardinality(peers) >= SampleSetSize
            /\ msgSet' = msgSet \cup { [kind |-> "query", src |-> p, dst |-> r, qcolor |-> color[HostMapping[r].node]]
                                      : r \in peers }
            /\ sample' = [sample EXCEPT ![p] = peers]
            /\ pc' = [pc EXCEPT ![p] = "waitReplies"]
  /\ UNCHANGED <<color, loopIters>>

\* A query process adopts the query's color if uncolored, then replies.
RespondQuery ==
  /\ \E m \in msgSet :
       /\ m.kind = "query"
       /\ LET n == HostMapping[m.dst].node IN
            /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN m.qcolor ELSE color[n]]
            /\ msgSet' = (msgSet \ {m}) \cup
                 {[kind |-> "reply", src |-> m.src, dst |-> m.dst, qcolor |-> color[n]]}
  /\ UNCHANGED <<pc, sample, loopIters>>

\* A loop process adopts a sampled color that meets the flip threshold.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] \in {"waitReplies", "sample"}
       /\ LET replies == { m \in msgSet : m.kind = "reply" /\ m.src = p }
              count(c) == Cardinality({ m \in replies : m.qcolor = c })
          IN
            /\ replies = sample[p]
            /\ IF count(0) >= PickFlipThreshold \/ count(1) >= PickFlipThreshold
                 THEN color' = [color EXCEPT ![HostMapping[p].node] =
                                   IF count(0) >= PickFlipThreshold THEN 0 ELSE 1]
                 ELSE color' = color
            /\ loopIters' = IF pc[p] = "sample" /\ loopIters[p] < SlushIterationCount
                              THEN [loopIters EXCEPT ![p] = loopIters[p] + 1]
                              ELSE loopIters
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ pc' = [pc EXCEPT ![p] = IF loopIters[p] < SlushIterationCount THEN "sample" ELSE "done"]
            /\ msgSet' = msgSet \ replies
  /\ UNCHANGED <<color, loopIters>>

\* After completing its iterations, the loop process terminates.
LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ msgSet' = msgSet \cup { [kind |-> "term", src |-> p, dst |-> r, qcolor |-> 0] : r \in SlushQueryProcess }
       /\ pc' = [pc EXCEPT ![p] = "waitTerm"]
  /\ UNCHANGED <<color, sample, loopIters>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "replyLoop"
       /\ \E p \in SlushLoopProcess : TermKind \in msgSet /\ [kind |-> "term", src |-> p, dst |-> q, qcolor |-> 0] \in msgSet
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, msgSet, sample, loopIters>>

Next == RequestAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(RequestAssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

TypeInvariant ==
  /\ color \in [Node -> {0, 1, NoColor}]
  /\ \A m \in msgSet : m.kind \in {"query", "reply", "term"}

====