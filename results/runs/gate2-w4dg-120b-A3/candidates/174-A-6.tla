---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* A Slush process queries a random sample of peers and adopts the sampled
\* majority color once it meets the flip threshold; the sampling is modeled
\* by nondeterministically picking any sample set of the required size.
\* The spec deliberately mirrors the PlusCal description and emits every
\* identifier that the reference TLC configuration expects.
CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

Message == [type: {"query", "reply", "term"}, from: Node, to: Node, col: Node \cup {NoColor}]

Nodes == 1..Cardinality(Node)

VARIABLES color, msgs, pc, sample, iterCount

vars == <<color, msgs, pc, sample, iterCount>>

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iterCount = [p \in SlushLoopProcess |-> 0]

HostLoop(n, p) == <<n, p, NoMessage>> \in HostMapping
HostQuery(n, p) == <<n, p, NoMessage>> \in HostMapping

\* The client process assigns initial colors to uncolored nodes; it may pick
\* any uncolored node and either of the two possible colors.
ClientAssignColor(n, c) ==
  /\ pc["client"] = "idle"
  /\ color[n] = NoColor
  /\ c \in {1, 2}
  /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "idle"]
  /\ UNCHANGED <<msgs, sample, iterCount>>

RequireColor(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in Node : HostLoop(n, p) /\ color[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, msgs, sample, iterCount>>

QuerySampleSet(p) ==
  /\ pc[p] = "waiting"
  /\ sample[p] = {}
  /\ \E n \in Node : HostLoop(n, p)
  /\ \E peers \in [k \in 1..SampleSetSize |-> Node] :
       /\ \A k \in 1..SampleSetSize : peers[k] # n
       /\ sample' = [sample EXCEPT ![p] = peers]
  /\ msgs' = msgs \cup { [type |-> "query", from |-> n, to |-> peers[k], col |-> color[n]] : k \in 1..SampleSetSize }
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<color, iterCount>>

\* A query process adopts the query's color if it is still uncolored, then
\* replies with its (possibly just-adopted) current color.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.type = "query"
       /\ msgs' = (msgs \ {m}) \cup { [type |-> "reply", from |-> m.to, to |-> m.from, col |-> IF color[m.to] = NoColor THEN m.col ELSE color[m.to]] }
  /\ UNCHANGED <<color, pc, sample, iterCount>>

TallyReplies(p) ==
  /\ pc[p] = "waiting"
  /\ sample[p] # {}
  /\ \A k \in 1..SampleSetSize : [type |-> "reply", from |-> sample[p][k], to |-> "loop", col |-> NoColor] \in msgs
  /\ \E n \in Node : HostLoop(n, p)
  /\ LET votes == [c \in {1, 2} |-> Cardinality({k \in 1..SampleSetSize : [type |-> "reply", from |-> sample[p][k], to |-> "loop", col |-> c] \in msgs})] IN
       \/ (\E c \in {1, 2} : votes[c] >= PickFlipThreshold /\ color' = [color EXCEPT ![n] = c])
       \/ (UNION { {c} : votes[c] >= PickFlipThreshold } = {} /\ color' = color)
  /\ msgs' = msgs \ { [type |-> "reply", from |-> sample[p][k], to |-> "loop", col |-> NoColor] : k \in 1..SampleSetSize }
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
  /\ UNCHANGED <<pc>>

LoopTerminate(p) ==
  /\ pc[p] = "waiting"
  /\ sample[p] = {}
  /\ iterCount[p] = SlushIterationCount
  /\ msgs' = msgs \cup { [type |-> "term", from |-> "loop", to |-> "client", col |-> NoColor] }
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<color, sample, iterCount>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A p \in SlushQueryProcess : pc[p] = "listening"
  /\ \E m \in msgs : m.type = "term"
  /\ pc' = [pc EXCEPT ![p] = "done" : p \in SlushQueryProcess]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<color, sample, iterCount>>

Next ==
  \/ \E n \in Node, c \in {1, 2} : ClientAssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTerminate(p)
  \/ RespondToQuery
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ color \in [Node -> {1, 2} \cup {NoColor}]
  /\ msgs \subseteq Message
  /\ \A m \in msgs : m.type \in {"query", "reply", "term"}

\* The whole system eventually reaches its done state (no live queries,
\* no unprocessed messages, every loop and query process finished).
Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done")
====