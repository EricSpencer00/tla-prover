---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* State vector
\* ----------------------------------------------------------------------
vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Placeholder definitions for the algorithm's initial condition and step.
\* The actual algorithm is imported from the sequential reachability
\* module; these definitions are only needed so that the TLA+ model
\* type‑checks.
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"

Next ==
  \/ /\ pc = "start"
     /\ Marked' = Marked \/ Frontier
     /\ Frontier' = {}
     /\ pc' = "done"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Graph‑theoretic primitives (provided by the reachability proofs module)
\* ----------------------------------------------------------------------
\* Successor relation (placeholder – the real definition lives in the
\* imported lemmas module).
Succ == [n \in Nodes |-> {}]

\* Reachability from a set of nodes (placeholder).
Reachable(S) == {}

\* ----------------------------------------------------------------------
\* Lemmas assumed from the reachability proofs module.
\* ----------------------------------------------------------------------
ASSUME Lemma1 == TRUE
ASSUME Lemma2 == TRUE
ASSUME Lemma3 == TRUE

\* ----------------------------------------------------------------------
\* Invariants required by the partial‑correctness proof
\* ----------------------------------------------------------------------
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in Succ[n] : s \in Marked \/ s \in Frontier

Inv2 ==
  (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

Inv3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS ==
  /\ Inv1
  /\ Inv2
  /\ Inv3

\* ----------------------------------------------------------------------
\* Properties (the set of safety properties to be checked)
\* ----------------------------------------------------------------------
PROPERTIES == INVARIANTS

====