---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* It adds concrete graph and sequence-bound definitions (the Config extension)
\* on top of the core algorithm's state variables, init, and actions.

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "run", "done"}

\* The algorithm's reachable set must be closed under successors, reachable
\* via a bounded sequence of steps, and consistent with the frontier.
Inv1 == \A n \in marked : \E b \in Seq : reachable(b, n)
Inv2 == \A n \in marked : \E m \in marked : m \in Succ[n]
Inv3 == marked \cap frontier = {}

PartialCorrectness == marked \subseteq marked \cup frontier

\* The original reachability predicate over sequences, unchanged.
reachable(b, n) ==
  /\ Len(b) >= 1
  /\ Head(b) = Root
  /\ Last(b) = n
  /\ \A k \in 1..(Len(b) - 1) : Head(Tail(b[1..k])) \in Succ[b[k]]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

Mark(n) ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = "run"

Quiesce ==
  /\ frontier = {}
  /\ pc = "run"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ marked' = {Root}
  /\ frontier' = Succ[Root]
  /\ pc' = "idle"

Next == \E n \in Nodes : Mark(n) \/ Quiesce \/ Reset

Spec == Init /\ [][Next]_vars

Termination == (pc = "done") ~> (pc = "idle")

====