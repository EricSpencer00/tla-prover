---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc
vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Concrete graph: each node has exactly two successors
\* This operator replaces the generic Succ operator in the cfg.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 0 -> {1, 2}
      []  n = 1 -> {2, 3}
      []  n = 2 -> {3, 0}
      []  n = 3 -> {0, 1}
  ]

\* ----------------------------------------------------------------------
\* Bounded sequence operator used in place of the infinite Seq
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Reachable set defined via bounded paths from Root
\* ----------------------------------------------------------------------
Reachable ==
  { n \in Nodes :
      \E p \in LimitedSeq(Nodes) :
        /\ Len(p) >= 1
        /\ p[1] = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1..Len(p)-1 :
             p[i+1] \in ConnectedToSomeButNotAll[p[i]]
  }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"

\* ----------------------------------------------------------------------
\* Algorithmic step: expand one node from the frontier
\* ----------------------------------------------------------------------
Expand ==
  /\ Frontier # {}
  /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ Marked')
        /\ pc' = "run"

\* ----------------------------------------------------------------------
\* Termination step: no more frontier nodes
\* ----------------------------------------------------------------------
Done ==
  /\ Frontier = {}
  /\ Marked' = Marked
  /\ Frontier' = Frontier
  /\ pc' = "done"

Next ==
  \/ Expand
  \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"start", "run", "done"}

Inv1 == (* successor closure *)
  \A n \in Marked :
    ConnectedToSomeButNotAll[n] \subseteq Marked

Inv2 == (* Marked equals the set of nodes reachable from Root *)
  Marked = Reachable

Inv3 == (* Frontier together with Marked equals Reachable while algorithm runs *)
  (pc # "done") => (Frontier \cup Marked = Reachable)

PartialCorrectness ==
  (pc = "done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====