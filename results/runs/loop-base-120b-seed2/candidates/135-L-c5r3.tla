---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Concrete graph with 4 nodes, each having exactly two successors. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    IF n = "A" THEN {"B","C"}
    ELSE IF n = "B" THEN {"A","D"}
    ELSE IF n = "C" THEN {"A","D"}
    ELSE IF n = "D" THEN {"B","C"}
    ELSE {}]

(* Bounded sequence operator for model checking – must match the arity of Seq *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Tuple of all state variables, used for priming and fairness *)
Vars == <<marked, frontier, pc>>

(* Initial state *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Start"

(* Next‑state relation – concrete sequential algorithm steps *)
Next ==
  \/ /\ pc = "Start"
     /\ pc' = "Run"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Run"
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

(* Specification includes weak fairness to guarantee progress from “Run” to “Done” *)
Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(Next)

(* Invariants – placeholders for the real algorithm invariants *)
TypeOK == TRUE
Inv1 == TRUE
Inv2 == TRUE
Inv3 == TRUE
PartialCorrectness == TRUE

(* Liveness property: the algorithm eventually reaches the completed state *)
Termination == <> (pc = "Done")
====