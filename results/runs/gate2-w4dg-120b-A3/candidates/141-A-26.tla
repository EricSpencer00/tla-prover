---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* A non-empty frontier means the algorithm is still running and the
\* loop is weakly fair in its action; a finite reachable set forces
\* eventual termination, which is why the invariant below only
\* requires a finite reachable set, not an empty frontier.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Either a fresh node: mark it and add its successors to the frontier,
\* or an already-marked node: simply remove it from the frontier.
Explore ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* Reachable[t] = nodes reachable from t via the graph's edges.
RECURSIVE ReachableFrom(_)
ReachableFrom(t) ==
  IF t \in Nodes
  THEN {t} \cup (UNION {ReachableFrom(s) : s \in Succ[t]})
  ELSE {}

ReachableSet == ReachableFrom(Root)

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup ReachableFrom(frontier) =
    marked \cup ReachableFrom(marked \cup frontier)

Inv3 ==
  ReachableSet = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableSet)

Termination == (Cardinality(ReachableSet) < \infinity) ~> (pc = "done")

\* The PlusCal front end creates Seq; the .cfg overrides it with a
\* finite version, so this operator only exists to keep the
\* front end happy -- it is never used directly.
LimitedSeq(S) == S

\* The .cfg replaces Succ with ConnectedToSomeButNotAll during
\* model checking. The operator is defined here so it exists.
ConnectedToSomeButNotAll(n) == Succ[n]

====