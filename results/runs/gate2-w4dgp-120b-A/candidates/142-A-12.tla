---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability, ReachableAlgs

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore(n) ==
  /\ pc = "idle"
  /\ pc' = "searching"
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED marked

Mark(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ pc' = "idle"
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}

Done ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : Explore(n) \/ Mark(n)
        \/ Done

Spec == Init /\ [][Next]_vars

Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : \A m \in Nodes : Edge(n, m) => (m \in marked \/ m \in frontier)

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

KeyLemma1 ==
  \A X \subseteq Nodes, Y \subseteq Nodes :
    ReachableFrom(X) \cup ReachableFrom(Y) = ReachableFrom(X \cup Y)

KeyLemma2 ==
  \A X \subseteq Nodes, n \in Nodes :
    ReachableFrom(X \cup {n}) = ReachableFrom(X) \cup ReachableFrom({n})

KeyLemma3 ==
  ReachableFrom({}) = {}

THEOREM TerminationPartial ==
  (pc = "done") => (marked = ReachableFrom(Root))

====