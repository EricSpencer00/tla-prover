---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {}
  THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == ReachFrom(S \ {x})
       IN rest \cup {x} \cup Succ[x]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "searching"

Explore(n) ==
  /\ n \in frontier
  /\ pc = "searching"
  /\ IF n \notin marked
     THEN /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
     ELSE /\ marked' = marked
          /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ frontier = {}
  /\ pc = "searching"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Done

PartialCorrectness ==
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
  /\ ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)
  /\ ReachFrom({Root}) = marked \cup ReachFrom(frontier)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Nodes : Explore(n))
  /\ SF_vars(Done)

Termination ==
  /\ \A n \in Nodes : Succ[n] \subseteq ReachFrom(Nodes)
  /\ \A n \in Nodes : n \notin Succ[n]
  /\ SF_vars(Done)
  /\ WF_vars(\E n \in Nodes : Explore(n))

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====