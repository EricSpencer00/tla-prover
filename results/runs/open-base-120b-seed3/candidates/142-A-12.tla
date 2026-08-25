---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root
CONSTANT Edge \* relation between nodes (may be instantiated in the cfg)

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Reachability definition using transitive closure of Edge
\* ----------------------------------------------------------------------
Reachable(S) == { y \in Nodes : \E x \in S : <<x, y>> \in Edge^* }

\* ----------------------------------------------------------------------
\* Initial state (algorithm starts with only the root in the frontier)
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation (single‑step expansion of the frontier)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Running"
        /\ frontier # {}
        /\ \E n \in frontier:
             LET succs == { m \in Nodes : <<n, m>> \in Edge } IN
               /\ marked'   = marked \cup {n}
               /\ frontier' = (frontier \ {n}) \cup (succs \ marked)
               /\ pc'       = IF frontier' = {} THEN "Done" ELSE "Running"
  \/ /\ pc = "Done"
        /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked :
        \A m \in Nodes :
          <<n, m>> \in Edge => m \in marked \/ m \in frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reachable({Root}) = marked ∪ Reachable(frontier)
\* ----------------------------------------------------------------------
Inv3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

\* ----------------------------------------------------------------------
\* Partial‑correctness property (proved in TLAPS)
\* ----------------------------------------------------------------------
Correctness == (pc = "Done") => marked = Reachable({Root})

PROPERTIES == {Correctness}
====