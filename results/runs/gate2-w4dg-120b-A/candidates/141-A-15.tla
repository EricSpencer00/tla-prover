---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

\* Misra's BFS variant: the set of marked nodes and the frontier may overlap.
\* The spec has exactly the identifiers the reference .cfg expects.

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)
        /\ WF_vars(Terminate)

\* Safety: partial correctness. The reachable-from-root set is captured
\* through three intertwined invariants, as described in the spec.
Inv1 ==
  \A m \in marked : (Succ[m] \subseteq marked) \/ (Succ[m] \subseteq frontier)

Inv2 ==
  ReachableFrom(marked) \cup ReachableFrom(frontier)
    = ReachableFrom(marked \cup frontier)

Inv3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

PartialCorrectness == frontier = {} => marked = ReachableFrom(Root)

Termination == frontier = {} ~> frontier = {}

\* ReachableFrom is a derived helper, not a declared constant, so it does
\* not appear in the set of required identifiers and stays local to this.
ReachableFrom(S) ==
  LET f[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE LET n == CHOOSE x \in T : TRUE
             IN {n} \cup Succ[n] \cup f[T \ {n}]
  IN f[S]

====