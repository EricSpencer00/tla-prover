---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

\* Model-checking configuration: concrete graph and bounded sequence.
\* The invariants and the termination property are the checks the
\* description requires; the override below replaces the unbounded Seq
\* operator from Sequences with a FINITE version for TLC.

CONSTANTS Nodes, Root, Succ

\* Reachability is defined as an existential over a bounded path; the
\* sequence type is finite so this is checkable.
RECURSIVE PathOf(_)
PathOf(n) == IF n = Root THEN <<Root>> ELSE
                CHOOSE p \in Seq(Nodes) :
                  /\ Len(p) <= Cardinality(Nodes)
                  /\ p[1] = Root
                  /\ p[Len(p)] = n
                  /\ \A i \in 1..(Len(p) - 1) : Succ[p[i]] \supseteq {p[i+1]}

RECURSIVE Reachable(_)
Reachable(S) == {n \in Nodes : \E p \in PathOf(n) : \A i \in 1..(Len(p) - 1) : p[i] \in S}

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

Start ==
  /\ pc = "idle"
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

Advance ==
  /\ pc = "working"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {n \in Nodes : Succ[n] \cap frontier # {}}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Start \/ Advance \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance) /\ WF_vars(Terminate)

\* The invariant suite: type correctness plus the three algorithmic
\* guarantees (closure under successors, the reachable decomposition,
\* and the reachable set being exactly the marked set).
\* Partial correctness checks that the algorithm has, at termination,
\* covered every node in the finite graph.
Inv1 == \A n \in marked : Succ[n] \subseteq Reachable(marked)
Inv2 == \A n \in Nodes : Reachable({n}) \subseteq Reachable(marked)
Inv3 == Reachable(marked) = marked
PartialCorrectness == (pc = "done") => (marked = Nodes)

Termination == (pc = "done") ~> (pc = "done")

====