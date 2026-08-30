---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Procs, Succ

SuccOf(x) == Succ[x]

VARIABLES marked, frontier, pc, selected, succs

vars == << marked, frontier, pc, selected, succs >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ selected \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Acquire(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ selected' = [selected EXCEPT ![p] = x]
       \/ succs' = [succs EXCEPT ![p] = SuccOf(x)]
       /\ frontier' = frontier \ {x}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ marked' = marked

Explore(p) ==
  /\ pc[p] = "working"
  /\ \E y \in succs[p] :
       /\ marked' = marked \cup {y}
       /\ frontier' = frontier \cup {y}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ selected' = [selected EXCEPT ![p] = Root]

Next ==
  \E p \in Procs : Acquire(p) \/ Explore(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Inv

ConnectedToSomeButNotAll(x) == SuccOf(x)

LimitedSeq(n) == IF n \in Nat THEN CHOOSE s \in Seq(1..n) : Len(s) = n ELSE "empty"

====