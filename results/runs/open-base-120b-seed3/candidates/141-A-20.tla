---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Constants *)
CONSTANTS Nodes, Root, SuccMap

(***************************************************************************)
(* Operators required by the .cfg substitution *)
ConnectedToSomeButNotAll(n) == SuccMap[n]

(***************************************************************************)
(* Replacement for Seq from Sequences *)
LimitedSeq(S) == Seq(S)

(***************************************************************************)
(* State variables *)
VARIABLES marked, frontier, pc

Vars == <<marked, frontier, pc>>

(***************************************************************************)
(* Helper definitions *)
SuccRel == { <<n, m>> : n \in Nodes, m \in ConnectedToSomeButNotAll(n) }

Reach(S) ==
  S \cup { t \in Nodes : \E s \in S : <<s, t>> \in TC(SuccRel) }

(***************************************************************************)
(* Initial state *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

(***************************************************************************)
(* Main action *)
Main ==
  \/ /\ pc = "Run"
     /\ frontier # {}
     /\ \E n \in frontier :
          \/ /\ n \notin marked
             /\ marked' = marked \cup {n}
             /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
             /\ pc' = "Run"
          \/ /\ n \in marked
             /\ marked' = marked
             /\ frontier' = frontier \ {n}
             /\ pc' = "Run"
  \/ /\ pc = "Run"
     /\ frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>

Next == Main

(***************************************************************************)
(* Specification *)
Spec == Init /\ [][Next]_Vars /\ WF_vars(Next)

(***************************************************************************)
(* Invariants *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  \A n \in marked :
    ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

Inv2 ==
  (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
  (pc = "Done") => (marked = Reach({Root}))

(***************************************************************************)
(* Liveness property *)
Termination == <> (pc = "Done")

=============================================================================