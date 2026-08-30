---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* Two possible colors for the consensus (a binary decision), plus an
\* uncolored state that only client-assigned nodes may start in.
\* Messages are queued in a set; ordering is intentionally left unconstrained.
\* Loop processes repeatedly sample peers and adopt a sufficiently popular color.
\* Query processes simply echo their node's current color back to the loop.
\* A client process assigns initial colors to uncolored nodes before looping begins.
\* Convergence to a single color is a probabilistic outcome, not a TLA+ property.

ASSUME HostMapping \subseteq (Node \X SlushLoopProcess \X SlushQueryProcess)

QueryMessage == [from: SlushLoopProcess, peer: SlushQueryProcess, col: {NoColor} \union {"c1", "c2"}]
QueryReply == [from: SlushQueryProcess, loop: SlushLoopProcess, col: {NoColor} \union {"c1", "c2"}]
LoopTerminate == [from: SlushLoopProcess]

VARIABLES nodeColor, messages, pc, sampleSet, iterationCount

vars == <<nodeColor, messages, pc, sampleSet, iterationCount>>

TypeInvariant ==
  /\ nodeColor \in [Node -> {NoColor} \union {"c1", "c2"}]
  /\ messages \subseteq (QueryMessage \union QueryReply \union LoopTerminate \union {NoMessage})
  /\ pc \in [SlushLoopProcess -> {"init", "sampling", "waiting", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [lp \in SlushLoopProcess |-> "init"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterationCount = [lp \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  \E n \in Node, c \in {"c1", "c2"} :
    /\ nodeColor[n] = NoColor
    /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sampleSet, iterationCount>>

HostOf(lp) ==
  CHOOSE n \in Node, qp \in SlushQueryProcess :
    <<n, lp, qp>> \in HostMapping

RequireColor(lp) ==
  /\ pc[lp] = "init"
  /\ nodeColor[HostOf(lp)] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, iterationCount>>

QuerySampleSet(lp) ==
  /\ pc[lp] = "sampling"
  /\ sampleSet[lp] = {}
  /\ iterationCount[lp] < SlushIterationCount
  /\ \E peers \in SUBSET SlushQueryProcess :
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
       /\ messages' = messages \union
            { [from |-> lp, peer |-> qp, col |-> nodeColor[HostOf(lp)]] : qp \in peers }
  /\ UNCHANGED <<nodeColor, pc, iterationCount>>

RespondToQuery(qp) ==
  \E m \in messages :
    /\ m \in QueryMessage
    /\ m.peer = qp
    /\ (nodeColor[HostOf(m.from)] = NoColor \/ nodeColor' = [nodeColor EXCEPT ![HostOf(m.from)] = m.col])
    /\ messages' = (messages \ {m}) \union
         { [from |-> qp, loop |-> m.from, col |-> nodeColor[HostOf(m.from)]] }
    /\ UNCHANGED <<pc, sampleSet, iterationCount>>

TallyReplies(lp) ==
  /\ pc[lp] = "sampling"
  /\ sampleSet[lp] # {}
  /\ \A qp \in sampleSet[lp] : [from |-> qp, loop |-> lp, col |-> {NoColor} \union {"c1", "c2"}] \in messages
  /\ LET replies == { r \in messages : r \in QueryReply /\ r.loop = lp }
         colCount(c) == Cardinality({ r \in replies : r.col = c })
         newCol == IF colCount("c1") >= PickFlipThreshold THEN "c1"
                   ELSE IF colCount("c2") >= PickFlipThreshold THEN "c2"
                   ELSE nodeColor[HostOf(lp)]
     IN nodeColor' = [nodeColor EXCEPT ![HostOf(lp)] = newCol]
  /\ messages' = messages \ { r \in messages : r \in QueryReply /\ r.loop = lp }
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
  /\ pc' = [pc EXCEPT ![lp] = IF iterationCount[lp] + 1 = SlushIterationCount
                              THEN "done" ELSE "sampling"]

LoopTerminate(lp) ==
  /\ pc[lp] = "sampling"
  /\ iterationCount[lp] = SlushIterationCount
  /\ messages' = messages \union {[from |-> lp]}
  /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ UNCHANGED <<nodeColor, sampleSet, iterationCount>>

QueryLoopExit ==
  /\ \A qp \in SlushQueryProcess : pc[HostOf(Choose lp \in SlushLoopProcess : <<HostOf(lp), lp, qp>> \in HostMapping)] = "done"
  /\ \A lp \in SlushLoopProcess : [from |-> lp] \in messages
  /\ \A qp \in SlushQueryProcess :
       \A m \in messages : (m \in QueryMessage /\ m.peer = qp) => FALSE
  /\ UNCHANGED vars

Next ==
  \/ ClientAssignColor
  \/ \E lp \in SlushLoopProcess : RequireColor(lp)
  \/ \E lp \in SlushLoopProcess : QuerySampleSet(lp)
  \/ \E qp \in SlushQueryProcess : RespondToQuery(qp)
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(QueryLoopExit)

\* Every process eventually reaches its done state, regardless of the
\* particular color convergence path the network takes.
Terminating == <>(\A lp \in SlushLoopProcess : pc[lp] = "done")

====