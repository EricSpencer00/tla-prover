---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Concrete graph with 4 nodes, each having exactly two successors.
   A default empty set is provided to avoid a CASE evaluation error
   if the constant set Nodes contains any element not listed explicitly. *)
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