---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE Succ(_)
Succ(S) == {y \in Nodes : \E x \in S : <<x, y>> \in Reachable.E}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN Succ({x}) \cup ReachableFrom(S \ {x})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "working"

Explore ==
  /\ pc = "working"
  /\ \E x \in frontier :
       /\ frontier' = (frontier \ {x}) \cup (Succ({x}) \ marked)
       /\ marked' = marked \cup Succ({x})
  /\ pc' = "working"

Done ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Explore \/ Done \/ Idle

Spec == Init /\ [][Next]_vars

Inductive ==
  /\ TypeOK
  /\ Succ(marked) \subseteq marked \cup frontier

FrontierDecomposition ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

CompleteExploration ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

TerminationSound == (pc = "done") => (marked = ReachableFrom(Root))

====