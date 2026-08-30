---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET add[S'] == UNION {N \in S' : {n \in Nodes : <<n, S'>> \in N}}
  IN IF S = add[S] THEN S ELSE ReachableFrom(add[S])

RECURSIVE ReachableFromRoot(_)
ReachableFromRoot(n) ==
  IF n = {} THEN {}
  ELSE LET r == CHOOSE x \in n : TRUE
           rest == n \ {r}
       IN {r} \cup ReachableFromRoot(rest \cup {y \in Nodes : <<r, y>> \in Nodes})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

StartStep ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "active"
  /\ UNCHANGED <<marked, frontier>>

ProcessFrontier ==
  /\ pc = "active"
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "idle"

AdvanceFrontier ==
  /\ pc = "active"
  /\ frontier = {}
  /\ frontier' = {n \in Nodes : \E m \in marked : <<m, n>> \in Nodes}
  /\ UNCHANGED <<marked, pc>>

Stalled ==
  /\ pc = "active"
  /\ frontier = {}
  /\ \A n \in Nodes : \A m \in marked : <<m, n>> \notin Nodes
  /\ pc' = "idle"
  /\ UNCHANGED <<marked, frontier>>

Next == StartStep \/ ProcessFrontier \/ AdvanceFrontier \/ Stalled

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A m \in marked : \A n \in Nodes : (<<m, n>> \in Nodes) => (n \in marked \/ n \in frontier)

Lemma1 ==
  \A S \in SUBSET Nodes : (Nodes \cup frontier) \subseteq ReachableFrom(Root)

Invariant2 ==
  (marked \cup ReachableFrom(frontier)) = ReachableFromRoot(Nodes)

Invariant3 ==
  ReachableFromRoot(Nodes) = marked \cup ReachableFrom(frontier)

Terminate == pc = "idle" /\ frontier = {}
TerminationOK == Terminate ~> Terminate

====