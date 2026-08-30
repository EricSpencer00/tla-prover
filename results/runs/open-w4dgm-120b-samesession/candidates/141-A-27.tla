---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE e \in S : TRUE IN Succ[n] \cup ReachFrom(S \ {n})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Misra's variant: the frontier may retain a node after marking it.
Explore(n) ==
  /\ n \in frontier
  /\ pc = "running"
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \E n \in Nodes : Explore(n)
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Done)

\* Every successor of a marked node is either already marked or on the frontier.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The reachable zone of (marked \cup frontier) equals that of marked plus frontier.
Inv2 ==
  ReachFrom(marked \cup frontier) = (ReachFrom(marked) \cup ReachFrom(frontier))

\* The reachable zone of the root is exactly the marked zone plus that of the frontier.
PartialCorrectness ==
  ReachFrom({Root}) = (marked \cup ReachFrom(frontier))

Inv3 == ReachFrom(Succ) = Succ

Terminating == \A n \in Nodes : (n \in frontier) ~> (n \notin frontier)

====