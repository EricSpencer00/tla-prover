---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, ReachabilityAlg, ReachabilityProofs

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(* Initial state: start with only the root in the frontier, nothing marked *)
(* ------------------------------------------------------------------- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "loop"

(* ------------------------------------------------------------------- *)
(* Next-state relation: the sequential Misra reachability algorithm   *)
(* ------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "loop"
        /\ frontier # {}
        /\ LET n == Choose(frontier) IN
           /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup
                           { s \in Succ[n] : s \notin marked }
           /\ pc'       = "loop"
  \/ /\ pc = "loop"
        /\ frontier = {}
        /\ pc' = "done"
        /\ UNCHANGED <<marked, frontier>>

(* ------------------------------------------------------------------- *)
(* Invariant 1: type correctness and successor condition               *)
(* ------------------------------------------------------------------- *)
Invariant1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"loop","done"}
  /\ \A n \in marked :
        \A s \in Succ[n] : s \in marked \/ s \in frontier

(* ------------------------------------------------------------------- *)
(* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier) *)
(* ------------------------------------------------------------------- *)
Invariant2 ==
  ReachableFrom(marked) \cup ReachableFrom(frontier)
    = ReachableFrom(marked \cup frontier)

(* ------------------------------------------------------------------- *)
(* Invariant 3: Reachable from the root equals marked ∪ Reachable(frontier) *)
(* ------------------------------------------------------------------- *)
Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

Invariants ==
  /\ Invariant1
  /\ Invariant2
  /\ Invariant3

(* ------------------------------------------------------------------- *)
(* Partial‑correctness property: when the algorithm terminates, the    *)
(* marked set equals the set of nodes reachable from the root.        *)
(* ------------------------------------------------------------------- *)
PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

Properties == PartialCorrectness

(* ------------------------------------------------------------------- *)
(* Specification                                                               *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

====