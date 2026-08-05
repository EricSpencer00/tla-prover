---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Misra's BFS variant: the visited set and the frontier may overlap.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Two cases are available from the frontier, chosen nondeterministically,
\* which is exactly what lets the frontier and marked sets overlap.
Explore ==
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ IF n \notin marked
          THEN /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
          ELSE /\ frontier' = frontier \ {n}
               /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is either already marked or still in the frontier.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The nodes reachable from what is already known (marked) and what is still to explore (frontier) together reach
\* exactly the nodes reachable from the union of those two sets.
Inv2 ==
  \A A \subseteq Nodes : (A \cup (UNION {Succ[m] : m \in A})) = (A \cup (UNION {Succ[m] : m \in (A \cup frontier)}))

\* Reachability from the root is exactly what is marked plus what is reachable from the frontier.
Inv3 ==
  (Root \cup (UNION {Succ[m] : m \in {Root}})) = (marked \cup (UNION {Succ[m] : m \in frontier}))

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in (Root \cup (UNION {Succ[m] : m \in {Root}})))

Termination ==
  (Root \cup (UNION {Succ[m] : m \in {Root}}) # {}) ~> (Root \cup (UNION {Succ[m] : m \in {Root}}) = {})

====