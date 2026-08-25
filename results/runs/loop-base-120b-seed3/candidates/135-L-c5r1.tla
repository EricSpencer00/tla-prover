---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

(*-------------------------------------------------------------------*)
(* Constants required by the configuration                           *)
(*-------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ

(*-------------------------------------------------------------------*)
(* Operator that provides a finite successor relation for each node *)
(* This operator will be substituted for the constant Succ by the .cfg *)
(*-------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
       [] n = 2 -> {3, 4}
       [] n = 3 -> {1, 4}
       [] n = 4 -> {1, 2}
       [] OTHER -> {}

(*-------------------------------------------------------------------*)
(* A finite version of the generic Seq operator, bounded by the      *)
(* number of nodes (here 4).                                          *)
(*-------------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-------------------------------------------------------------------*)
(* Variables of the sequential reachability algorithm                *)
(*-------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-------------------------------------------------------------------*)
(* Type correctness invariant                                         *)
(*-------------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "process", "done"}

(*-------------------------------------------------------------------*)
(* Helper definition of reachable nodes using bounded sequences      *)
(*-------------------------------------------------------------------*)
Reachable ==
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) >= 1
        /\ Head(p) = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1 .. (Len(p) - 1) :
             p[i+1] \in ConnectedToSomeButNotAll(p[i])
  }

(*-------------------------------------------------------------------*)
(* Invariant 1: successor closure                                     *)
(*-------------------------------------------------------------------*)
Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

(*-------------------------------------------------------------------*)
(* Invariant 2: reachability decomposition (frontier nodes are the   *)
(* first unmarked nodes on some path from the root)                 *)
(*-------------------------------------------------------------------*)
Inv2 ==
  \A n \in frontier :
    \E p \in LimitedSeq(Nodes) :
      /\ Len(p) >= 1
      /\ Head(p) = Root
      /\ p[Len(p)] = n
      /\ \A i \in 1 .. (Len(p) - 1) :
           p[i+1] \in ConnectedToSomeButNotAll(p[i])
      /\ \A i \in 1 .. (Len(p) - 2) :
           p[i] \notin marked

(*-------------------------------------------------------------------*)
(* Invariant 3: marked set equals the set of reachable nodes         *)
(*-------------------------------------------------------------------*)
Inv3 ==
  marked = Reachable

(*-------------------------------------------------------------------*)
(* Partial correctness: when the algorithm terminates, all reachable*)
(* nodes have been marked (same as Inv3, but stated as a property)  *)
(*-------------------------------------------------------------------*)
PartialCorrectness ==
  (pc = "done") => marked = Reachable

(*-------------------------------------------------------------------*)
(* Initial state                                                     *)
(*-------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"
  /\ TypeOK

(*-------------------------------------------------------------------*)
(* Transition relation                                               *)
(*-------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "init"
     /\ pc' = "process"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "process"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "process"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup
                         (ConnectedToSomeButNotAll(n) \ (marked \cup {n}))
          /\ pc' = "process"
          /\ UNCHANGED <<>>

(*-------------------------------------------------------------------*)
(* Specification                                                     *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-------------------------------------------------------------------*)
(* Invariants to be checked                                          *)
(*-------------------------------------------------------------------*)
INVARIANT == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness

(*-------------------------------------------------------------------*)
(* Liveness property: algorithm eventually reaches the done state   *)
(*-------------------------------------------------------------------*)
Termination == <> (pc = "done")
====