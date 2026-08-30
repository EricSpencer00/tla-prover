---- MODULE Slush ----
EXTENDS Naturals

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Types of in-flight messages (a query, a query reply, and a termination notice).
Message == [mtype: {"query", "queryReply", "termination"}, src: Node, dst: Node, c: {NoColor} \union {"c1", "c2"}]

VARIABLES color, msgs, pc, sampleSet, iterations

vars == <<color, msgs, pc, sampleSet, iterations>>

\* Each Slush process is linked to one node via the host mapping; it runs its
\* own loop and shares one message buffer with every other node's process.
NodeOf(p) == CHOOSE n \in Node : <<n, p>> \in HostMapping

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess |-> "start"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client arbitrarily assigns an initial color to an uncolored node.
ClientAssignColor ==
  /\ \E n \in Node, c \in {"c1", "c2"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sampleSet, iterations>>

RequireColor(p) ==
  /\ p \in SlushLoopProcess
  /\ pc[p] = "awaitingColor"
  /\ color[NodeOf(p)] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<color, msgs, sampleSet, iterations>>

\* Each round samples a fixed-size set of peer processes at random.
QuerySampleSet(p) ==
  /\ pc[p] = "idle"
  /\ iterations[p] < SlushIterationCount
  /\ \E peers \subseteq SlushQueryProcess \ NodeOf(p):
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
       /\ msgs' = msgs \union {[mtype |-> "query", src |-> NodeOf(p), dst |-> NodeOf(q), c |-> color[NodeOf(p)]] : q \in peers}
  /\ pc' = [pc EXCEPT ![p] = "collecting"]
  /\ UNCHANGED <<color, iterations>>

RespondQuery ==
  /\ \E m \in msgs :
       /\ m.mtype = "query"
       /\ LET n == m.dst IN
            /\ msgs' = (msgs \ {m}) \union
                 {[mtype |-> "queryReply", src |-> n, dst |-> m.src, c |-> IF color[n] = NoColor THEN m.c ELSE color[n]]}
            /\ IF color[n] = NoColor THEN color' = [color EXCEPT ![n] = m.c] ELSE color' = color
            /\ UNCHANGED <<pc, sampleSet, iterations>>

TallyReplies(p) ==
  /\ pc[p] = "collecting"
  /\ Cardinality(sampleSet[p]) > 0
  /\ \A q \in sampleSet[p] : [mtype |-> "queryReply", src |-> q, dst |-> NodeOf(p), c |-> "c1"] \in msgs \/ [c |-> "c2"] \in msgs
  /\ LET replies == {m \in msgs : m.mtype = "queryReply" /\ m.dst = NodeOf(p)} IN
       LET counts == [c \in {"c1", "c2"} |-> Cardinality({m \in replies : m.c = c})] IN
         IF counts["c1"] >= PickFlipThreshold \/ counts["c2"] >= PickFlipThreshold
           THEN color' = [color EXCEPT ![NodeOf(p)] = IF counts["c1"] >= PickFlipThreshold THEN "c1" ELSE "c2"]
           ELSE color' = color
  /\ msgs' = msgs \ {m \in msgs : m.mtype = "queryReply" /\ m.dst = NodeOf(p)}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ iterations' = [iterations EXCEPT ![p] = iterations[p] + 1]
  /\ pc' = [pc EXCEPT ![p] = "idle"]

LoopTerminate(p) ==
  /\ p \in SlushLoopProcess
  /\ pc[p] = "idle"
  /\ iterations[p] = SlushIterationCount
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ msgs' = msgs \union {[mtype |-> "termination", src |-> NodeOf(p), dst |-> NoNode, c |-> NoColor]}
  /\ UNCHANGED <<color, sampleSet, iterations>>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess : pc[q] = "start"
  /\ \A lp \in SlushLoopProcess : [mtype |-> "termination", src |-> NodeOf(lp), dst |-> NoNode, c |-> NoColor] \in msgs
  /\ pc' = [q \in SlushQueryProcess |-> "done"]
  /\ UNCHANGED <<color, msgs, sampleSet, iterations>>

Next ==
  \/ ClientAssignColor
  \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTerminate(p)
  \/ RespondQuery
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ WF_vars(ClientAssignColor)
  /\ \A p \in SlushLoopProcess : WF_vars(RequireColor(p)) /\ WF_vars(QuerySampleSet(p)) /\ WF_vars(TallyReplies(p)) /\ WF_vars(LoopTerminate(p))
  /\ WF_vars(RespondQuery)
  /\ WF_vars(QueryLoopExit)

\* The type invariant checks that colors and message formats stay within their
\* declared domains; it never rules out a bug that merely slows convergence.
TypeInvariant ==
  /\ \A n \in Node : color[n] \in {NoColor} \union {"c1", "c2"}
  /\ \A m \in msgs :
       /\ m.mtype \in {"query", "queryReply", "termination"}
       /\ m.src \in Node
       /\ m.dst \in Node \union {NoNode}
       /\ m.c \in {NoColor} \union {"c1", "c2"}

Termination == <>(\A p \in SlushLoopProcess \union SlushQueryProcess : pc[p] = "done")

====