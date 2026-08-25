---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* ------------------------------------------------------------------- *)
(*  Auxiliary definitions *)

MaxLen == 5

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

(* This operator will be substituted for Succ by the .cfg file *)
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]

(* Reachability of a set of nodes via Succ (or its substitution) *)
Reach(S) ==
  { n \in Nodes :
      \E T \subseteq Nodes :
        /\ S \subseteq T
        /\ (\A m \in T : Succ[m] \subseteq T)
        /\ n \in T }

(* ------------------------------------------------------------------- *)
(*  Invariants *)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \/ frontier

Inv2 ==
  (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  (frontier = {}) => marked = Reach({Root})

(* ------------------------------------------------------------------- *)
(*  Initial state *)

Init ==
  /\ pc = "run"
  /\ marked = {}
  /\ frontier = {Root}
  /\ TypeOK

(* ------------------------------------------------------------------- *)
(*  Next-state relation *)

Next ==
  \/ /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>
  \/ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = "run"
        \/ /\ n \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
           /\ pc' = "run"

(* ------------------------------------------------------------------- *)
(*  Specification *)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(*  Liveness property *)

Termination == <> (frontier = {})

====