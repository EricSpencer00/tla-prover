---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, state
vars == <<marked, frontier, state>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ state \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ state = "running"

\* Actions: nondeterministically pick a frontier node and either mark it and
\* add its successors to the frontier, or drop it if already marked.
Step ==
  /\ frontier # {}
  /\ \E x \in frontier :
       IF x \notin marked
       THEN /\ marked' = marked \cup {x}
            /\ frontier' = frontier \cup Succ[x]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {x}
  /\ state' = "running"

Terminate ==
  /\ frontier = {}
  /\ state' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

\* Helper: nodes reachable from a set via repeated Succ expansion.
ReachableFrom(S) ==
  LET RECURSIVE Reach(S) ==
       IF S = {} THEN {}
       ELSE LET n == CHOOSE m \in S : TRUE IN Succ[n] \cup Reach(S \ {n})
  IN Reach(S)

\* Invariant 1: every successor of a marked node is still reachable from an
\* explored or frontier node -- frontier and marked may overlap.
Inv1 ==
  \A n \in Nodes :
    n \in marked => (Succ[n] \subseteq marked) \/ (Succ[n] \cap frontier # {})

\* Invariant 2: the union of marked and what the frontier can still reach
\* equals what the combined set (marked \cup frontier) can reach.
Inv2 ==
  \A S \in SUBSET Nodes :
    (ReachableFrom(S \cup frontier) \marked) \cup ReachableFrom(frontier) =
      ReachableFrom(S \cup frontier)

\* Invariant 3: Reachable from the root is exactly marked plus what the
\* frontier can still reach -- a consequence of the overlap, not disjointness.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == Inv3

Termination == (frontier # {}) ~> (frontier = {})

====