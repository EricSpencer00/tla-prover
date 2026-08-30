---- MODULE ReachableProofs ----
EXTENDS ReachableSeq, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "working"

Mark(n) ==
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = pc

Expand(n) ==
  /\ n \in marked
  /\ frontier' = frontier \cup {m \in Nodes : m \notin marked \cup frontier}
  /\ pc' = pc
  /\ UNCHANGED marked

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Terminate
  \/ \E n \in Nodes : Mark(n) \/ Expand(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Expand(Root))
  /\ WF_vars(Mark(Root))
  /\ \A n \in Nodes : WF_vars(Expand(n)) /\ WF_vars(Mark(n))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

ClosedUnderSuccessor ==
  \A n \in marked : \A m \in Nodes : (n \in marked /\ m \in Nodes /\ m \in successors(n)) => (m \in marked \/ m \in frontier)

Invariant1 ==
  /\ TypeOK
  /\ ClosedUnderSuccessor

Invariant2 ==
  marked \cup ReachableFrom(Sigma, frontier) = ReachableFrom(Sigma, marked \cup frontier)

Invariant3 ==
  ReachableFrom(Sigma, {Root}) = marked \cup ReachableFrom(Sigma, frontier)

TheoremTermination ==
  pc = "done" => marked = ReachableFrom(Sigma, {Root})

INVARIANTS == <<Invariant1, Invariant2, Invariant3>>
PROPERTIES == <<TheoremTermination>>
====