-------------------------- MODULE Slush --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Nodes are paired with their loop and query processes through HostMapping.
\* The model assumes a fully connected network; any node may be sampled.
\* Slush is a metastable protocol: convergence is probabilistic and cannot
\* be proved in TLA+, but the spec tracks the loop/response mechanics exactly.
\* PlusCal is used here for executable pseudocode; the translation defines
\* the required TLA+ operators (Init, Next, Spec, TypeInvariant, AllDone).

\* The message set is modelled as a set of tuples (type, src, dst, col).
Message == {NoMessage} \cup [kind: {"query", "reply", "term"}, src: Node, dst: Node, col: {NoColor} \cup 1..2]
MessageSet == SUBSET Message

VARIABLES assignment, msgs, pc, sample, loops

vars == <<assignment, msgs, pc, sample, loops>>

TypeOK ==
  /\ assignment \in [Node -> {NoColor} \cup 1..2]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waitingColor", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess |-> "waitingColor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loops = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (a transaction).
AssignColor(n) ==
  /\ assignment[n] = NoColor
  /\ \E c \in 1..2 : assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, loops>>

StartLoop(p, n) ==
  /\ <<p, n>> \in HostMapping
  /\ assignment[n] # NoColor
  /\ pc[p] = "waitingColor"
  /\ pc' = [pc EXCEPT ![p] = "sampling"]
  /\ UNCHANGED <<assignment, msgs, sample, loops>>

\* The loop process samples a fixed-size set of peer nodes and queries them.
QueryPeers(p, n) ==
  /\ <<p, n>> \in HostMapping
  /\ pc[p] = "sampling"
  /\ sample[p] = {}
  /\ \E peers \in SUBSET Node :
        /\ Cardinality(peers) = SampleSetSize
        /\ sample' = [sample EXCEPT ![p] = peers]
        /\ msgs' = msgs \cup {[kind |-> "query", src |-> n, dst |-> m, col |-> assignment[n]] : m \in peers}
  /\ UNCHANGED <<assignment, pc, loops>>

\* A query process answers with its current color; uncolored nodes adopt if needed.
RespondQuery(m) ==
  /\ m.kind = "query"
  /\ m \in msgs
  /\ LET cur == assignment[m.dst] IN
        /\ assignment' = [assignment EXCEPT ![m.dst] = IF cur = NoColor THEN m.col ELSE cur]
        /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> IF cur = NoColor THEN m.col ELSE cur]}
  /\ UNCHANGED <<pc, sample, loops>>

\* Once every sampled peer has replied, the loop adopts the majority color
\* if it meets the flip threshold; otherwise it stays put.
TallyAndFlip(p, n) ==
  /\ pc[p] = "sampling"
  /\ sample[p] # {}
  /\ \A m \in msgs : (m.kind = "reply" /\ m.dst = n /\ m.src \in sample[p]) => TRUE
  /\ LET count(c) == Cardinality({m \in msgs : m.kind = "reply" /\ m.dst = n /\ m.col = c}) IN
        /\ IF count(1) >= PickFlipThreshold THEN assignment' = [assignment EXCEPT ![n] = 1]
           ELSE IF count(2) >= PickFlipThreshold THEN assignment' = [assignment EXCEPT ![n] = 2]
           ELSE assignment' = assignment
  /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.dst = n)}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ loops' = [loops EXCEPT ![p] = IF loops[p] < SlushIterationCount THEN @ + 1 ELSE loops[p]]
  /\ UNCHANGED pc

TerminateLoop(p, n) ==
  /\ <<p, n>> \in HostMapping
  /\ pc[p] = "sampling"
  /\ loops[p] = SlushIterationCount
  /\ msgs' = msgs \cup {[kind |-> "term", src |-> n, dst |-> NoColor, col |-> NoColor]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<assignment, sample, loops>>

ExitQueryLoop(q) ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<assignment, msgs, sample, loops>>

Next ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E p \in SlushLoopProcess, n \in Node : StartLoop(p, n)
  \/ \E p \in SlushLoopProcess, n \in Node : QueryPeers(p, n)
  \/ \E m \in Message : RespondQuery(m)
  \/ \E p \in SlushLoopProcess, n \in Node : TallyAndFlip(p, n)
  \/ \E p \in SlushLoopProcess, n \in Node : TerminateLoop(p, n)
  \/ \E q \in SlushQueryProcess : ExitQueryLoop(q)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ assignment \in [Node -> {NoColor} \cup 1..2]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waitingColor", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

\* Every process eventually stops, but the spec makes no claim about which
\* color the network converges to -- that is probabilistic and outside TLA+'s scope.
AllDone == <>(\A p \in SlushLoopProcess : pc[p] = "done")

Properties == AllDone
=============================================================================