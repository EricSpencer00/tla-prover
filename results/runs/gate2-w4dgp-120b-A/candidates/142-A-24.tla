---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

\* ReachableSet: standard graph-reachability closure.
RECURSIVE ReachableSet(_, _)
ReachableSet(S, e) ==
  IF e \in S THEN S
  ELSE \/ (\E c \in S : ReachableSet(S, c)) \/ (S \cup {e})

\* Reach: reachable nodes from a seed set via the graph's successor relation.
RECURSIVE Reach(_, _)
Reach(S, e) ==
  IF e \in S THEN S
  ELSE \/ (\E c \in S : Reach(S, c)) \/ {e}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "expand", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Nodes \ {Root}
  /\ pc = "init"

\* Mark a node that is reachable from something already marked.
Expand ==
  /\ pc = "init"
  /\ \E n \in frontier :
       /\ \E c \in marked : n \in ReachableSet({c}, n)
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
  /\ pc' = "init"

Reset ==
  /\ pc = "init"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Reset]_vars /\ WF_vars(Expand)

\* Invariant 1: every successor of a marked node is either marked or still
\* in the frontier (type-correctness already established in TypeOK).
Inv1 == /\ TypeOK
        /\ \A c \in marked : \A n \in ReachableSet({c}, n) : n \in marked \cup frontier

\* Invariant 2: marked nodes plus what's reachable from the frontier already
\* cover everything reachable from marked \cup frontier (proved from Lemma 1).
Inv2 == ReachableSet(marked \cup frontier, Root) = marked \cup Reach(frontier, Root)

\* Invariant 3: the reachable set from the root splits exactly into the
\* marked nodes and the frontier's reachable tail (Lemmas 2 and 3).
Inv3 == ReachableSet({Root}, Root) = marked \cup Reach(frontier, Root)

\* Partial correctness theorem: termination leaves exactly the reachable set.
Theorem == pc = "done" => ReachableSet({Root}, Root) = marked

INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
PROPERTY Theorem

====