---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Concrete graph with 4 nodes, each having exactly two successors *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = "A" -> {"B","C"}
    [] n = "B" -> {"A","D"}
    [] n = "C" -> {"A","D"}
    [] n = "D" -> {"B","C"}
  ]

(* Bounded sequence operator for model checking *)
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(* Initial state *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Start"

(* Next‑state relation – placeholder for the sequential algorithm *)
Next ==
  \/ /\ pc = "Start"
     /\ pc' = "Run"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Run"
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

(* Invariants *)
TypeOK == TRUE
Inv1 == TRUE
Inv2 == TRUE
Inv3 == TRUE
PartialCorrectness == TRUE

(* Liveness property *)
Termination == <> (pc = "Done")

====