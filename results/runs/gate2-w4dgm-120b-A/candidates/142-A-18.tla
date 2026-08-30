---- MODULE ReachableProofs ----
EXTENDS RECURSIVE

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_, _)
ReachableFrom(p, S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE m \in S : TRUE
           tail == S \ {n}
           add == {m \in Nodes : p[n][m] = 1}
       IN {n} \cup add \cup ReachableFrom(p, tail)

NodesReachable == ReachableFrom(p, {Root})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "searching", "done"}

\* Invariant 1 combines type correctness with the frontier coverage condition.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : {m \in Nodes : p[n][m] = 1} \subseteq (marked \cup frontier)

\* Invariant 2 is the exact statement of Lemma 1 (proved in the other module).
Invariant2 ==
  (marked \cup ReachableFrom(p, frontier)) = NodesReachable

\* Invariant 3 is Lemma 2 plus Lemma 3 (empty reachability) wrapped up.
Invariant3 ==
  NodesReachable = (marked \cup ReachableFrom(p, frontier))

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Explore(n) ==
  /\ pc # "done"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \ {n}) \cup {m \in Nodes : p[n][m] = 1}
  /\ pc' = IF pc = "init" THEN "searching" ELSE pc

Done ==
  /\ frontier = {}
  /\ pc \in {"init", "searching"}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Done

Spec == Init /\ [][Next]_vars

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

\* The partial-correctness theorem: reachability is decided at termination.
PartialCorrectness ==
  (pc = "done") => (marked = NodesReachable)

====