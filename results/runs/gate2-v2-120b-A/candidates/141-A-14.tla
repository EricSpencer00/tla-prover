---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, TLC

(*----------------------------------------------------------------------
  Constants
----------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*----------------------------------------------------------------------
  Derived constants
----------------------------------------------------------------------*)
Node == Nodes

(*----------------------------------------------------------------------
  State variables
----------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*----------------------------------------------------------------------
  Type correctness invariant
----------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in {"Running", "Done"}

(*----------------------------------------------------------------------
  Initial predicate
----------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(*----------------------------------------------------------------------
  Helper: any element from a non-empty set
----------------------------------------------------------------------*)
Pick(F) == CHOOSE n \in F: TRUE

(*----------------------------------------------------------------------
  Main action (two nondeterministic cases)
----------------------------------------------------------------------*)
BFS ==
    /\ pc = "Running"
    /\ frontier # {}
    /\ LET n == Pick(frontier) IN
       IF n \notin marked THEN
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = "Running"
       ELSE
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = "Running"

(*----------------------------------------------------------------------
  Termination action
----------------------------------------------------------------------*)
Terminate ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

(*----------------------------------------------------------------------
  Next-state relation
----------------------------------------------------------------------*)
Next == BFS \/ Terminate

(*----------------------------------------------------------------------
  Specification
----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*----------------------------------------------------------------------
  Invariants
----------------------------------------------------------------------*)

(* Inv1: every successor of a marked node is in marked or frontier *)
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* Inv2: the union of marked and nodes reachable from frontier equals
        nodes reachable from the union of marked and frontier *)
Inv2 ==
    ReachFrom(marked \cup frontier) =
    marked \cup ReachFrom(frontier)

(* Inv3: the set of nodes reachable from Root equals the marked set plus
        nodes reachable from frontier *)
Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

(* Partial correctness: when terminated, marked equals reachable from Root *)
PartialCorrectness ==
    pc = "Done" => marked = ReachFrom({Root})

(*----------------------------------------------------------------------
  Reachability helper (definition used in Inv2, Inv3, PartialCorrectness)
----------------------------------------------------------------------*)
ReachFrom(S) ==
    LET
        Acc(seen, frontier) ==
            IF frontier = {} THEN seen
            ELSE
                LET n == CHOOSE x \in frontier: TRUE IN
                    Acc(seen \cup {n}, (frontier \ {n}) \cup Succ[n])
    IN Acc(S, S)

(*----------------------------------------------------------------------
  Liveness property (Termination)
----------------------------------------------------------------------*)
Termination ==
    <> (pc = "Done")

=============================================================================