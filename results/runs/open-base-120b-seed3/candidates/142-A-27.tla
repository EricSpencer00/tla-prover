---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachAlg, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(* ----------------------------------------------------------------------
   Initial state (placeholder – the concrete algorithm supplies the real
   definition).  The actual Init predicate will be supplied by the
   sequential reachability algorithm module.
   ---------------------------------------------------------------------- *)
Init == TRUE

(* ----------------------------------------------------------------------
   Next action (placeholder – the concrete algorithm supplies the real
   definition).  The actual Next predicate will be supplied by the
   sequential reachability algorithm module.
   ---------------------------------------------------------------------- *)
Next == TRUE

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(* ----------------------------------------------------------------------
   Invariant 1: type correctness and successor condition
   ---------------------------------------------------------------------- *)
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(* ----------------------------------------------------------------------
   Invariant 2: reachable-from‑frontier property (Lemma 1)
   ---------------------------------------------------------------------- *)
Inv2 ==
  (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

(* ----------------------------------------------------------------------
   Invariant 3: marked set equals reachable from the root (Lemmas 2‑3)
   ---------------------------------------------------------------------- *)
Inv3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == { Inv1, Inv2, Inv3 }

(* ----------------------------------------------------------------------
   No liveness properties are expressed (TLAPS does not yet support them)
   ---------------------------------------------------------------------- *)
PROPERTIES == {}

====