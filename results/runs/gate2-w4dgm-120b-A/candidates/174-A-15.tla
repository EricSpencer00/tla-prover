---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Two possible colors; NoColor = the uncolored initial state.
Color == {"red", "blue", NoColor}

\* Each node pairs exactly one loop process and one query process via HostMapping.
\* A process p is a SlushLoopProcess iff some tuple (n, p, q) is in HostMapping and
\* a process q is a SlushQueryProcess iff some tuple (n, p, q) is in HostMapping.
Fulfills(p) == {n \in Node : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping}
Molds(q) == {n \in Node : \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping}
Illuminate(p) == {q \in SlushQueryProcess : <<Fulfills(p), p, q>> \in HostMapping}
ReplyChannel(q) == CHOOSE p \in SlushLoopProcess : <<Molds(q), p, q>> \in HostMapping

VARIABLES assignment, inbox, pc, sampleSet, iterations

vars == <<assignment, inbox, pc, sampleSet, iterations>>

TypeOK ==
  /\ assignment \in [Node -> Color]
  /\ inbox \subseteq [msgType: {"query", "queryReply", "termination"}, to: SlushLoopProcess \union SlushQueryProcess, from: SlushLoopProcess \union SlushQueryProcess, col: Color]
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess -> {"idle", "waiting", "responding", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess |-> "idle"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client assigns a random (adversarial, possibly all the same) color to an
\* uncolored node -- the only source of initial colors in the network.
AssignColor(n, c) ==
  /\ pc[ReplyChannel(Molds(n))] = "idle"
  /\ assignment[n] = NoColor
  /\ assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<inbox, pc, sampleSet, iterations>>

\* Each loop process waits for its host node to be colored before starting any round.
RequireColor(p) ==
  /\ pc[p] = "idle"
  /\ assignment[Fulfills(p)] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<assignment, inbox, sampleSet, iterations>>

\* The loop process randomly samples a fixed number of other nodes and asks them
\* for their current colors.
QuerySampleSet(p, S) ==
  /\ pc[p] = "waiting"
  /\ iterations[p] < SlushIterationCount
  /\ S \subseteq Node
  /\ S \cap {Fulfills(p)} = {}
  /\ Cardinality(S) = SampleSetSize
  /\ inbox' = inbox \union {[msgType |-> "query", to |-> ReplyChannel(q), from |-> p, col |-> assignment[Fulfills(p)]] : q \in Illuminate(p)}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
  /\ pc' = [pc EXCEPT ![p] = "responding"]
  /\ UNCHANGED <<assignment, iterations>>

\* A query process adopts the query's color if it is still uncolored, then replies.
RespondToQuery(q, m) ==
  /\ pc[q] = "idle"
  /\ m.msgType = "query"
  /\ m.to = q
  /\ assignment[Molds(q)] = NoColor
  /\ assignment' = [assignment EXCEPT ![Molds(q)] = m.col]
  /\ inbox' = (inbox \ {m}) \union {[msgType |-> "queryReply", to |-> ReplyChannel(q), from |-> q, col |-> m.col]}
  /\ pc' = [pc EXCEPT ![q] = "responding"]
  /\ UNCHANGED <<sampleSet, iterations>>

\* The loop process waits for replies from its full sample, then adopts any color
\* that reaches the flip threshold, which is what drives the whole network to one.
TallyReplies(p) ==
  /\ pc[p] = "responding"
  /\ \A n \in sampleSet[p] : \E m \in inbox : m.msgType = "queryReply" /\ m.from = ReplyChannel(n) /\ m.to = p
  /\ \E c \in {"red", "blue"} :
       /\ Cardinality({n \in sampleSet[p] : \E m \in inbox : m.msgType = "queryReply" /\ m.from = ReplyChannel(n) /\ m.col = c}) >= PickFlipThreshold
       /\ assignment' = [assignment EXCEPT ![Fulfills(p)] = c]
  /\ inbox' = {m \in inbox : ~(m.msgType = "queryReply" /\ m.to = p /\ m.from \in {ReplyChannel(n) : n \in sampleSet[p]})}
  /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
  /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
  /\ pc' = [pc EXCEPT ![p] = "waiting"]

LoopTerminate(p) ==
  /\ pc[p] = "waiting"
  /\ iterations[p] = SlushIterationCount
  /\ inbox' = inbox \union {[msgType |-> "termination", to |-> ReplyChannel(q), from |-> p, col |-> NoColor] : q \in Illuminate(p)}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<assignment, sampleSet, iterations>>

QueryLoopExit(q) ==
  /\ pc[q] = "responding"
  /\ \A p \in SlushLoopProcess : [msgType |-> "termination", to |-> ReplyChannel(q), from |-> p, col |-> NoColor] \in inbox
  /\ inbox' = {m \in inbox : ~(m.msgType = "termination" /\ m.to = q)}
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<assignment, sampleSet, iterations>>

Next ==
  \/ \E n \in Node, c \in {"red", "blue"} : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess, S \in SUBSET Node : QuerySampleSet(p, S)
  \/ \E q \in SlushQueryProcess, m \in inbox : RespondToQuery(q, m)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ \E p \in SlushLoopProcess : LoopTerminate(p)
  \/ \E q \in SlushQueryProcess : QueryLoopExit(q)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E q \in SlushQueryProcess : QueryLoopExit(q))

\* Structural safety: the assignment map is always well-typed and every message
\* in flight conforms to one of the three defined message schemas.
TypeInvariant == TypeOK

\* Every process (loop or query) eventually reaches its done state.
Termination == \A p \in SlushLoopProcess \union SlushQueryProcess : TRUE ~> (pc[p] = "done")

====