---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* Reachable(v) = nodes reachable from v in the directed graph; Succ is the
\* successor relation, and Reachable is defined recursively.
RECURSIVE Reachable(_)
Reachable(v) ==
  IF \E w \in Nodes : w \in Succ[v] THEN
    LET reached == {w \in Nodes : \E c \in Succ[v] : w \in Reachable(c)} \cup Succ[v]
    IN reached
  ELSE Succ[v]

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"running", "done"}

\* The overlapping-mark-and-frontier scheme: a node in frontier that is already
\* marked is simply removed, never re-marked. That overlap is the whole point.
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

MarkAndExpand(n) ==
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup Succ[n]
Explore(n) ==
  /\ marked' = marked
  /\ frontier' = frontier \ {n}
Backtrack ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in frontier : MarkAndExpand(n) \/ Explore(n)
  \/ Backtrack

Spec == Init /\ [][Next]_vars

\* Invariant 1: every successor of a marked node is either already marked or
\* still waiting in the frontier; nothing in the graph's reachable closure is
\* lost between the two sets.
Inv1 ==
  \A n \in Nodes : n \in marked => Succ[n] \subseteq marked \cup frontier

\* Invariant 2: the union of marked nodes and everything reachable from the
\* frontier is already everything reachable from whatever is marked plus
\* whatever is in the frontier.
Inv2 ==
  Reachable(marked \cup frontier) = marked \cup Reachable(frontier)

\* Invariant 3: the nodes reachable from the root consist of the marked nodes
\* together with everything reachable from the frontier.
Inv3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

\* Safety: at termination the algorithm's marked set is exactly the reachable
\* set. The three invariants above are what makes that equality provable.
PartialCorrectness == pc = "done" => marked = Reachable({Root})

Termination == \A n \in Nodes : True => <>(pc = "done")

\* Operators that the .cfg substitutes in the model -- left side is the name
\* expected by the .cfg; right side is the replacement definition used here.
ConnectedToSomeButNotAll(n) == Cardinality(Succ[n]) > 0 /\ Cardinality(Succ[n]) < Cardinality(Nodes)
LimitedSeq(n) == CHOOSE s \in Sequences(Nodes) : Len(s) = 1

====