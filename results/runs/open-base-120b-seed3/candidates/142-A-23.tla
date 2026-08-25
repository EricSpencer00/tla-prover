---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

\* Assume the graph is given by a constant edge relation.
CONSTANT Edge \* Edge \subseteq Nodes \X Nodes

ASSUME Root \in Nodes
ASSUME Edge \subseteq Nodes \X Nodes

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Succ(n) == { m \in Nodes : <<n, m>> \in Edge }

\* Reachable nodes from a set S via any finite path using Edge.
ReachFrom(S) ==
  { n \in Nodes :
      \E p \in Seq(Nodes) :
        /\ Len(p) # 0
        /\ p[1] \in S
        /\ p[Len(p)] = n
        /\ \A i \in 1..Len(p)-1 : <<p[i], p[i+1]>> \in Edge }

\* ----------------------------------------------------------------------
\* Initialization (the concrete algorithm supplies its own, we give a simple
\* placeholder consistent with the description)
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* ----------------------------------------------------------------------
\* Next-step relation (placeholder; real algorithm steps are imported)
\* ----------------------------------------------------------------------
Next == TRUE

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<|marked, frontier, pc|>_

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked :
        \A s \in Succ(n) : s \in marked \/ s \in frontier

\* Invariant 2: marked ∪ ReachFrom(frontier) = ReachFrom(marked ∪ frontier)
Inv2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

\* Invariant 3: ReachFrom({Root}) = marked ∪ ReachFrom(frontier)
Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

Invariants == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* Partial‑correctness property (final theorem)
\* ----------------------------------------------------------------------
Terminated == pc = "done"

PartialCorrectness == [] (Terminated => marked = ReachFrom({Root}))

Properties == PartialCorrectness

============================================================================