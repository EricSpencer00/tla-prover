---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*---------------------------------------------------------------------*)
(* Concrete graph definition: each node has exactly two successors   *)
(* This operator will be substituted for Succ by the .cfg file.       *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2,3}
    [] n = 2 -> {3,4}
    [] n = 3 -> {4,1}
    [] OTHER -> {1,2}
  ]

(*---------------------------------------------------------------------*)
(* LimitedSeq is a finite version of Seq, bounded by |Nodes|        *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*---------------------------------------------------------------------*)
(* Reachable set defined using bounded sequences                     *)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
  }

(*---------------------------------------------------------------------*)
(* Initial state                                                     *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

(*---------------------------------------------------------------------*)
(* One step of the sequential Misra reachability algorithm           *)
Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier
        IN /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
           /\ pc'       = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

(*---------------------------------------------------------------------*)
(* Specification                                                     *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*---------------------------------------------------------------------*)
(* Invariants                                                       *)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == frontier \subseteq Nodes \ marked

Inv3 == marked = Reachable

PartialCorrectness == (pc = "done") => (marked = Reachable)

(*---------------------------------------------------------------------*)
(* Liveness property                                                  *)
Termination == <> (pc = "done")

=============================================================================