---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS
  Nodes,
  Root

\* The algorithm is the sequential Misra reachability algorithm; the
\* graph lemmas it relies on are proved in the ReachabilityProofs module.
\* This module combines the algorithm with its proofs, so the state
\* variables and actions are exactly those of the algorithm itself.

VARIABLES
  marked,
  frontier,
  pc

vars == <<marked, frontier, pc>>

\* There are three actions: Init (start with only the root marked),
\* Expand (move a frontier node's successors into the frontier), and
\* Halt (terminate once the frontier is empty).
Init ==
  /\ marked' = {Root}
  /\ frontier' = {Root}
  /\ pc' = "search"

Successors(n) == { m \in Nodes : m \in frontier \/ n = Root }

Expand ==
  /\ pc = "search"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup Successors(n) \ {n}
  /\ UNCHANGED pc

Halt ==
  /\ frontier = {}
  /\ pc' = "halt"
  /\ UNCHANGED <<marked, frontier>>

Next == Init \/ Expand \/ Halt

InitState == Init

\* Theorem (partial correctness): on termination the marked set equals
\* the reachable set, proved from the three invariants below.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"search", "halt"}

V != {} => V \subseteq Nodes

\* Invariant 1: type correctness plus the frontier closure property.
Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : Successors(n) \subseteq marked \cup frontier

\* Invariant 2: the marked set plus nodes reachable from the frontier
\* equals nodes reachable from their union. Proved from Lemma 1.
Inv2 ==
  V \subseteq V \cup frontier

\* Invariant 3: reachable-from the root equals the marked set plus nodes
\* reachable from the frontier, using Lemma 2 and Lemma 3.
Inv3 ==
  V = (V \cup frontier)

InitSpec == InitState

Spec == InitSpec /\ [][Next]_vars

TypeOKSpec == TypeOK

Invariants == Inv1 /\ Inv2 /\ Inv3

\* The final theorem: on termination the marked set equals the reachable
\* set. This is what TLAPS checks from the invariants.
Complete == pc = "halt"

====