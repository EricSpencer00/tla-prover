---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(x) ==
  /\ pc = "running"
  /\ x \in frontier
  /\ \/ /\ x \notin marked
        /\ marked' = marked \cup {x}
        /\ frontier' = frontier \cup Succ[x]
     \/ /\ x \in marked
        /\ frontier' = frontier \ {x}
        /\ marked' = marked
  /\ IF frontier \cup {x} \cup Succ[x] = {}
       THEN pc' = "done"
       ELSE pc' = pc

Next == \E x \in Nodes : Explore(x)

Spec == Init /\ [][Next]_vars

Inv1 == \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

Inv2 == ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

Inv3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == \A x \in Nodes : ((x \in marked) <=> (x \in ReachableFrom({Root})))

Termination == pc = "done"

ConnectedToSomeButNotAll(x) == Succ[x]

\* Finite truncation of the built-in Seq operator so the model stays finite for TLC.
LimitedSeq(i) == IF i >= 1 THEN i ELSE 0

====