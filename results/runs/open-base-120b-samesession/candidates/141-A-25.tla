---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(*----------------------------------------------------------------------
  Operators required by the configuration
----------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S)

(*----------------------------------------------------------------------
  State variables
----------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*----------------------------------------------------------------------
  Helper definitions
----------------------------------------------------------------------*)
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

Reach(S) == TC(SuccRel, S)      \* set of nodes reachable from any element of S

(*----------------------------------------------------------------------
  Initial state
----------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

(*----------------------------------------------------------------------
  Next-state relation
----------------------------------------------------------------------*)
RunStep ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ IF n \notin marked
                THEN /\ marked' = marked \cup {n}
                     /\ frontier' = frontier \cup Succ[n]
                ELSE /\ marked' = marked
                     /\ frontier' = frontier \ {n}
          /\ pc' = "Run"
          /\ UNCHANGED <<>>

Terminate ==
    /\ pc = "Run"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == RunStep \/ Terminate \/ Stutter

(*----------------------------------------------------------------------
  Specification
----------------------------------------------------------------------*)
Spec == Init /\ [] [Next]_<<marked, frontier, pc>>

(*----------------------------------------------------------------------
  Invariants
----------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = Reach({Root})

(*----------------------------------------------------------------------
  Liveness property
----------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================