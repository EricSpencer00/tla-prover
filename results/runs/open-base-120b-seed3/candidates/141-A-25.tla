---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

(*-----------------------------------------------------------------
  Helper definitions for reachability
-----------------------------------------------------------------*)
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(SuccRel) }

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == Reach(marked \cup frontier) = marked \cup Reach(frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == frontier = {} => marked = Reach({Root})

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = pc
    \/ /\ frontier = {}
       /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Liveness property
-----------------------------------------------------------------*)
Termination == []<>(frontier = {})

(*-----------------------------------------------------------------
  Operator substitutions required by the .cfg
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= 10 }

=============================================================================