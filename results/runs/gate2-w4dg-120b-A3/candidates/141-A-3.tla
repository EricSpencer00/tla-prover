---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* A single sequential process explores the graph, keeping a set of visited (marked)
\* nodes and a frontier of nodes still to explore.  In Misra's variant the frontier
\* may overlap the visited set, which is what makes parallelism simple.
VARIABLES visited, frontier, pc

vars == << visited, frontier, pc >>

TypeOK ==
  /\ visited \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"running", "terminated"}
  /\ Root \in Nodes

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The main action: one node from the frontier either gets marked and its
\* successors added to the frontier, or is removed if already marked.
Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ frontier' = frontier \ {n}
       /\ IF n \in visited
            THEN visited' = visited
            ELSE visited' = visited \cup {n}
                 /\ frontier' = frontier' \cup Succ[n]
  /\ pc' = IF frontier' = {} THEN "terminated" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is already visited or still waiting in the frontier.
Inv1 == \A n \in visited : Succ[n] \subseteq visited \cup frontier

\* The nodes reachable from "visited \cup frontier" are exactly those reachable from
\* "visited" plus those reachable from "frontier".
Inv2 == ReachableFrom(visited \cup frontier) = visited \cup ReachableFrom(frontier)

\* The nodes reachable from the root are the visited nodes plus those reachable from
\* the frontier that is still to be explored.
Inv3 == ReachableFrom({Root}) = visited \cup ReachableFrom(frontier)

PartialCorrectness == pc = "terminated" => visited = ReachableFrom({Root})

\* A finite reachable set guarantees termination under weak fairness: the frontier
\* cannot stay non-empty forever.
Termination == (\A x \in Nodes : x \in ReachableFrom({Root}) => x \in Nodes)
                 ~> (pc = "terminated")

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET x == CHOOSE y \in S : TRUE
        rest == ReachableFrom(S \ {x})
    IN {x} \cup Succ[x] \cup rest

\* PlusCal generates a bounded sequence type "Seq".  The .cfg replaces it with a
\* finite (bounded) version called LimitedSeq, which keeps the model checkable.
LimitedSeq == Seq

\* The .cfg also substitutes this operator for Succ, so Succ[n] is never infinite.
ConnectedToSomeButNotAll == Succ

====