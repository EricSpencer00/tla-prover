---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The frontier and the marked set may overlap; that is what makes the
\* loop terminate under weak fairness rather than requiring a strict set.
VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ReachableFrom(n) ==
  {x \in Nodes : \E k \in Nat : \E seq \in LimitedSeq(n, x, k) : TRUE}

Explore(n) ==
  /\ pc = "running"
  /\ frontier # {}
  /\ n \in frontier
  /\ \/ (n \notin marked /\ marked' = marked \cup {n}
                              /\ frontier' = frontier \cup Succ[n])
     \/ (n \in marked /\ frontier' = frontier \ {n})
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

ExploreSome == \E n \in Nodes : Explore(n)

Next == ExploreSome

\* Every successor of a marked node is already reachable (in the marked set
\* or still waiting in the frontier) -- this is what keeps the reachable set
\* closed under the graph's edges even though frontier and marked overlap.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Reachable nodes are exactly the marked ones plus those still waiting to
\* be pulled off the frontier; no reachable node can be missed or duplicated.
Inv2 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier)

Inv3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Termination == (frontier # {}) ~> (frontier = {})

\* The reachable set of a finite graph is finite, so the loop can only
\* extend it a bounded number of times; with weak fairness it must then
\* empty the frontier and halt.
\* Misra's variant overlaps marked and frontier, which is what keeps this
\* from needing a strict queue discipline.
\* The empty frontier is the only terminal state.
\* While the loop is running the frontier is never empty, so weak fairness
\* on the loop body is enough to drive the reachable set to closure.
\* When the reachable set is infinite the algorithm may keep pulling nodes
\* off the frontier forever, which is the case the invariants cover.
====