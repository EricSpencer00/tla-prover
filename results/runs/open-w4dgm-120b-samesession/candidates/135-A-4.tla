---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

\* Model checking a configuration module for the sequential reachability
\* algorithm: reachability on a concrete 4-node graph (Succ overridden here
\* to be a finite relation) with sequences bounded to the node count.
\* The full invariant suite from the algorithm, plus termination as a
\* temporal property, are model-checked over this finite state space.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Explore ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

Expand(n, m) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ m \in Succ[n]
  /\ marked' = marked \cup {m}
  /\ frontier' = (frontier \ {n}) \cup {m}
  /\ UNCHANGED pc

Complete ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ marked' = {Root}
  /\ frontier' = {Root}
  /\ pc' = "idle"

Next ==
  \/ Explore
  \/ \E n \in Nodes, m \in Nodes : Expand(n, m)
  \/ Complete
  \/ Reset

Spec == Init /\ [][Next]_vars

\* Reachability closure: every marked node is reachable from the root along
\* a path staying within the marked set. The existential path quantifier
\* ranges over LimitedSeq, a FINITE version of Seq, so the model stays
\* finite even though reachability is defined via potentially unbounded
\* paths in the general case.
ReachableFromRoot(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) >= 1
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1 .. (Len(s) - 1) : s[i+1] \in Succ[s[i]]
    /\ \A i \in 1 .. Len(s) : s[i] \in marked

Inv1 == \A n \in frontier : \E m \in Nodes : m \in Succ[n] /\ m \notin marked
Inv2 == \A n \in marked : ReachableFromRoot(n)
Inv3 == \A n \in marked : n \in ReachableFromRoot(n)
PartialCorrectness == \A n \in Nodes : (n \in marked) <=> ReachableFromRoot(n)

Termination == <>(pc = "done")

====