---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------*)
(*  Constants required by the .cfg file                               *)
(*--------------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*--------------------------------------------------------------------*)
(*  Type definitions                                                  *)
(*--------------------------------------------------------------------*)
Node == Nodes

(*--------------------------------------------------------------------*)
(*  State variables                                                   *)
(*--------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------*)
(*  Helper definitions                                                *)
(*--------------------------------------------------------------------*)
Successors(n) == { m \in Nodes : TRUE } \* placeholder; the actual
                               \* graph is defined in the
                               \* extended reachability module.

ReachableFrom(S) ==
    LET R == RECURSIVE R(_)
        R(S) == S \cup UNION { Successors(n) : n \in R(S) }
    IN R(S)

(*--------------------------------------------------------------------*)
(*  Initial predicate                                                 *)
(*--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

(*--------------------------------------------------------------------*)
(*  Actions                                                          *)
(*--------------------------------------------------------------------*)
Next ==
    \/ /\ pc = "Loop"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup
                           { s \in Successors(n) : s \notin marked }
            /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

(*--------------------------------------------------------------------*)
(*  Specification formula                                            *)
(*--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------*)
(*  Safety invariants (the three key invariants)                     *)
(*--------------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Successors(n) : s \in marked \/ s \in frontier

Inv2 ==
    marked \cup ReachableFrom(frontier) =
    ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(*--------------------------------------------------------------------*)
(*  Theorem (partial correctness)                                    *)
(*--------------------------------------------------------------------*)
THEOREM PartialCorrectness ==
    \A s \in ReachableFrom({Root}) : s \in marked

=============================================================================