---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(*--------------------------------------------------------------------*)
(* Concrete graph definition (used via operator substitution)        *)
(*--------------------------------------------------------------------)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  []  n = 2 -> {3, 4}
  []  n = 3 -> {1, 4}
  []  n = 4 -> {1, 2}
  []  OTHER -> {}

(*--------------------------------------------------------------------*)
(* Bounded sequence operator                                            *)
(*--------------------------------------------------------------------)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------*)
(* Reachability definition using bounded sequences                    *)
(*--------------------------------------------------------------------)
ReachableSet ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ Head(s) = Root
        /\ Last(s) = n
        /\ \A i \in 1..(Len(s)-1) :
            s[i+1] \in ConnectedToSomeButNotAll(s[i]) }

(*--------------------------------------------------------------------*)
(* State variables                                                     *)
(*--------------------------------------------------------------------)
VARIABLES Marked, Frontier, pc

(*--------------------------------------------------------------------*)
(* Initial state                                                       *)
(*--------------------------------------------------------------------)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Init"

(*--------------------------------------------------------------------*)
(* Transition relation                                                 *)
(*--------------------------------------------------------------------)
Next ==
  \/ /\ pc = "Init"
     /\ pc' = "Step"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "Step"
     /\ \E n \in Frontier :
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup ConnectedToSomeButNotAll(n)
          /\ pc'       = IF Frontier' = {} THEN "Done" ELSE "Step"
          /\ UNCHANGED pc
  \/ /\ pc = "Done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(*--------------------------------------------------------------------*)
(* Specification                                                       *)
(*--------------------------------------------------------------------)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*--------------------------------------------------------------------*)
(* Invariants                                                          *)
(*--------------------------------------------------------------------)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Init", "Step", "Done"}

Inv1 == \A n \in Marked : ConnectedToSomeButNotAll(n) \subseteq Marked \cup Frontier

Inv2 == Frontier \cap Marked = {}

Inv3 == Marked = ReachableSet

PartialCorrectness ==
  /\ pc = "Done"
  => Marked = ReachableSet

(*--------------------------------------------------------------------*)
(* Liveness property                                                   *)
(*--------------------------------------------------------------------)
Termination == <> (pc = "Done")

====