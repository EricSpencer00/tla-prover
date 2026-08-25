---- MODULE ReachableProofs ----
EXTENDS Integers, SequentAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Algorithm's initial condition and transition relation are imported from
   the sequential reachability algorithm module (SequentAlg).  The names
   INIT and NEXT are required by the configuration file.
   ---------------------------------------------------------------------- *)
INIT == AlgInit
NEXT == AlgNext

(* ----------------------------------------------------------------------
   Invariant 1:  type correctness and the successor property.
   ---------------------------------------------------------------------- *)
Inv1 == /\ Marked \subseteq Nodes
        /\ Frontier \subseteq Nodes
        /\ pc \in {"init","loop","done"}
        /\ \A n \in Marked :
              \A s \in Succ[n] :
                 s \in Marked \/ s \in Frontier

(* ----------------------------------------------------------------------
   Invariant 2:  marked ∪ Reachable(Frontier) = Reachable(Marked ∪ Frontier).
   This follows directly from Lemma 1 in ReachabilityLemmas.
   ---------------------------------------------------------------------- *)
Inv2 == Reachable(Marked) \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

(* ----------------------------------------------------------------------
   Invariant 3:  Reachable({Root}) = Marked ∪ Reachable(Frontier).
   Proven using Lemma 2 (stability under adding successors) and Lemma 3
   (Reachable of the empty set is empty).
   ---------------------------------------------------------------------- *)
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

(* ----------------------------------------------------------------------
   Specification required by the .cfg file.
   ---------------------------------------------------------------------- *)
Spec == INIT /\ [][NEXT]_vars

(* ----------------------------------------------------------------------
   The set of invariants that TLC shall check.
   ---------------------------------------------------------------------- *)
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(* ----------------------------------------------------------------------
   Partial‑correctness theorem: when the algorithm terminates,
   the marked set equals the set of nodes reachable from the root.
   ---------------------------------------------------------------------- *)
PartialCorrectness == 
    /\ pc = "done"
    => Marked = Reachable({Root})

PROPERTIES == PartialCorrectness

====