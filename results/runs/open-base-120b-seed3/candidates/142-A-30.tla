---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachAlg, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------- *)
(*  Initial state                                                     *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(* ------------------------------------------------------------------- *)
(*  Next-state relation                                               *)
(* ------------------------------------------------------------------- *)
Next ==
    \/ /\ pc = "run"
       /\ \E n \in frontier:
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked')
            /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(*  Invariants                                                       *)
(* ------------------------------------------------------------------- *)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes
    /\ pc \in {"run", "done"}
    /\ \A n \in marked :
         \A s \in Succ[n] : s \in marked \/ s \in frontier

Inv2 ==
    /\ marked \cup ReachableFrom(frontier) = 
       ReachableFrom(marked \cup frontier)

Inv3 ==
    /\ ReachableFrom({Root}) = 
       marked \cup ReachableFrom(frontier)

Invariants ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

(* ------------------------------------------------------------------- *)
(*  Safety property (partial correctness)                            *)
(* ------------------------------------------------------------------- *)
Termination == pc = "done"

Properties ==
    Termination => marked = ReachableFrom({Root})

(* ------------------------------------------------------------------- *)
(*  Specification                                                     *)
(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

====