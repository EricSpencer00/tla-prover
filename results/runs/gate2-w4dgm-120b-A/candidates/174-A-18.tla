---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol (the simplest member of the Snow family) is a         *)
(* metastable consensus protocol: loop processes repeatedly sample random     *)
(* peers and adopt a popular opinion, causing the network to converge on a    *)
(* single color.  Because TLA+ has no probabilistic features, this spec is     *)
(* only executable pseudocode -- it cannot model the convergence property.    *)

\* Nodes have an owner loop process and an owner query process, linked by a   *
\* host mapping; each loop process runs its own Slush iteration loop.        *

CONSTANTS
  Node,               \* the nodes (participants) in the network
  SlushLoopProcess,   \* the distinct looping processes (one per node)
  SlushQueryProcess,  \* the distinct query processes (one per node)
  HostMapping,        \* set of triples [node |-> n, loop |-> lp, query |-> qp]
  SlushIterationCount,\* per-loop iteration bound
  SampleSetSize,      \* number of peers sampled per round
  PickFlipThreshold,  \* replies of one color needed to flip
  NoColor,            \* sentinel meaning "uncolored"
  NoMessage           \* sentinel meaning "no message"

Message == [kind: {"query", "reply", "done"}, from: Node, to: Node, col: NoColor..2]

VARIABLES color, messages, pc, sampleSet, iterCount

TypeOK ==
  /\ color \in [Node -> NoColor..2]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting", "counting", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

\* A loop process may begin only once its host node has a color assigned.
HostOf(lp) == CHOOSE n \in Node : \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping
QueryOf(n) == CHOOSE qp \in SlushQueryProcess : \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterCount = [lp \in SlushLoopProcess |-> 0]

\* The client process keeps assigning random colors to uncolored nodes.
ClientAssignColor(n) ==
  /\ color[n] = NoColor
  /\ \E c \in 0..2 : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, iterCount>>

RequireColor(lp) ==
  /\ pc[lp] = "idle"
  /\ color[HostOf(lp)] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "waiting"]
  /\ UNCHANGED <<color, messages, sampleSet, iterCount>>

QuerySampleSet(lp) ==
  /\ pc[lp] = "waiting"
  /\ iterCount[lp] < SlushIterationCount
  /\ Cardinality(Node) > 1
  /\ \E S \in SUBSET (Node \ {HostOf(lp)}):
       /\ Cardinality(S) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = S]
  /\ messages' = messages \cup
       { [kind |-> "query", from |-> HostOf(lp), to |-> n, col |-> color[HostOf(lp)]] : n \in sampleSet[lp] }
  /\ pc' = [pc EXCEPT ![lp] = "counting"]
  /\ UNCHANGED <<color, iterCount>>

\* A query process adopts the query's color if it is uncolored, then replies.
RespondToQuery(n, q) ==
  /\ [kind |-> "query", from |-> q, to |-> n, col |-> NoColor + 1] \in messages
  /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN q ELSE color[n]]
  /\ messages' = (messages \ {[kind |-> "query", from |-> q, to |-> n, col |-> NoColor + 1]})
       \cup {[kind |-> "reply", from |-> n, to |-> q, col |-> color[n]]}
  /\ UNCHANGED <<pc, sampleSet, iterCount>>

TallyReplies(lp) ==
  /\ pc[lp] = "counting"
  /\ \A n \in sampleSet[lp]: [kind |-> "reply", from |-> n, to |-> HostOf(lp), col |-> NoColor + 1] \in messages
  /\ LET rcolor == [c \in 0..2 |-> Cardinality({n \in sampleSet[lp] :
                         [kind |-> "reply", from |-> n, to |-> HostOf(lp), col |-> c] \in messages})]
     IN color' = IF \E c \in 0..2 : rcolor[c] >= PickFlipThreshold
                 THEN [color EXCEPT ![HostOf(lp)] = CHOOSE c \in 0..2 : rcolor[c] >= PickFlipThreshold]
                 ELSE color
  /\ messages' = messages \ {[kind |-> "reply", from |-> n, to |-> HostOf(lp), col |-> NoColor + 1] : n \in sampleSet[lp]}
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
  /\ pc' = IF iterCount[lp] + 1 >= SlushIterationCount THEN "done" ELSE "waiting"

LoopTerminate(lp) ==
  /\ pc[lp] = "done"
  /\ [kind |-> "done", from |-> HostOf(lp), to |-> NoMessage, col |-> NoColor] \notin messages
  /\ messages' = messages \cup
       {[kind |-> "done", from |-> HostOf(lp), to |-> NoMessage, col |-> NoColor]}
  /\ UNCHANGED <<color, pc, sampleSet, iterCount>>

QueryLoopExit(qp) ==
  /\ pc[qp] = "idle"
  /\ \A lp \in SlushLoopProcess : [kind |-> "done", from |-> HostOf(lp), to |-> NoMessage, col |-> NoColor] \in messages
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, messages, sampleSet, iterCount>>

\* Every loop process must finish before any query process may exit.
Next ==
  \/ \E n \in Node : ClientAssignColor(n)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp) \/ TallyReplies(lp) \/ LoopTerminate(lp)
  \/ \E lp \in SlushLoopProcess : \E S \in SUBSET (Node \ {HostOf(lp)}):
       /\ Cardinality(S) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = S]
       /\ pc' = [pc EXCEPT ![lp] = "counting"]
       /\ UNCHANGED <<color, messages, iterCount>>
  \/ \E n \in Node, qp \in SlushQueryProcess : RespondToQuery(n, qp)
  \/ \E qp \in SlushQueryProcess : QueryLoopExit(qp)

Spec == Init /\ [][Next]_<<color, messages, pc, sampleSet, iterCount>>

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = "done")

====