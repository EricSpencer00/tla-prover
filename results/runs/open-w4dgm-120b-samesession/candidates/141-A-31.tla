---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Succ is the graph's edge relation. The .cfg file substitutes a bounded
\* connectedness operator for Succ, so Succ is not constrained here except
\* by the model's constants and the invariants.

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN Succ[n] \cup ReachableFrom(S \ {n})

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The frontier and the marked set may overlap; the algorithm removes a
\* node from the frontier only once it is already marked.
Explore(n) ==
  /\ n \in frontier
  /\ pc = "running"
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Explore(n))
        /\ WF_vars(Terminate)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

\* Children of a marked node are accounted for in the marked set or the
\* frontier; since those two may overlap, this is not a partitioning.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Termination == pc = "terminated"

\* Succ is substituted by ConnectedToSomeButNotAll from the .cfg.
ConnectedToSomeButNotAll == Succ

\* The .cfg substitutes LimitedSeq for Seq, so Seq is not exported.
LimitedSeq == Seq
====