---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*-----------------------------------------------------------------
  Functions
-----------------------------------------------------------------*)
ReachableFrom(S) ==
  LET R == RECURSIVE R(_) == 
      IF S = {} THEN {} 
      ELSE S \cup R({ y \in Nodes : \E x \in S : y \in Succ[x] })
  IN R(S)

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  TypeOK invariant (type correctness)
-----------------------------------------------------------------*)
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"Running", "Done"}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"
  /\ TypeOK

(*-----------------------------------------------------------------
  Main action
-----------------------------------------------------------------*)
PickNode ==
  CHOOSE n \in frontier :
    IF n \in marked THEN
      /\ marked' = marked
      /\ frontier' = frontier \ {n}
    ELSE
      /\ marked' = marked \cup {n}
      /\ frontier' = frontier \cup Succ[n]

Next ==
  IF pc = "Running" THEN
    IF frontier = {} THEN
      /\ pc' = "Done"
      /\ UNCHANGED <<marked, frontier>>
    ELSE
      /\ pc' = "Running"
      /\ PickNode
  ELSE
    UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Inv1 ==
  \A m \in marked :
    \A s \in Succ[m] : s \in frontier \/ s \in marked

Inv2 ==
  \A F \in SUBSET Nodes :
    \A M \in SUBSET Nodes :
      (ReachableFrom(F) \cup M) = ReachableFrom(F \cup M)

Inv3 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom({Root})

PartialCorrectness ==
  pc = "Done" => marked = ReachableFrom({Root})

(*-----------------------------------------------------------------
  Termination property (finite reachable set)
-----------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================