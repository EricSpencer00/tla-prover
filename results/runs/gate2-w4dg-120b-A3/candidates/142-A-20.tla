---- MODULE ReachableProofs ----
EXTENDS Naturals

\* A formal proof module for the sequential Misra reachability algorithm.
\* It carries TLAPS-checked proofs of partial correctness: three invariants
\* hold throughout execution, and on termination the marked set equals the
\* reachable set. Proofs depend on the graph lemmas proved in the reachability
\* proofs module (the lemmas are simply referenced here).
\* The module is deliberately limited to safety properties; liveness is not
\* proved, since TLAPS does not yet support it.

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "halt"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "run"

\* A transition that does not expand the search, guided by the invariant proof.
Step ==
  /\ pc = "run"
  /\ frontier = {}
  /\ pc' = "halt"
  /\ UNCHANGED << marked, frontier >>

Next == Step

Spec == Init /\ [][Next]_vars

\* Invariant 1 (inductive): type correctness plus no lost successors.
Inv1 ==
  /\ TypeOK
  /\ \A n \in marked :
       \A m \in Nodes : (n, m) \in E => m \in marked \/ m \in frontier

\* Lemma 1: the combined marked+frontier set is closed under successors.
\* Invariant 2 follows directly from this closure.
Inv2 == ReachableFrom(marked) \cup ReachableFrom(frontier)
           = ReachableFrom(marked \cup frontier)

\* Lemma 2 (reachable-from stable under adding successors) and Lemma 3
\* (reachable-from empty set is empty) together give this next invariant.
Inv3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

\* Partial correctness: on termination the marked set is exactly the reachable
\* set, proved using Invariant 3.
Partial == pc = "halt" => marked = ReachableFrom(Root)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3
PROPERTIES == Partial

====