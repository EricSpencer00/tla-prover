---- MODULE Reachable ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

MarkedSucs == { y \in Nodes : \E x \in marked : y \in Succ[x] }

\* Misra: frontier and marked may overlap, so successors may be
\* reachable through either.
FrontierSucs == { y \in Nodes : \E x \in frontier : y \in Succ[x] }

TotalReachable == { y \in Nodes : \E x \in marked \cup frontier : y \in Succ[x] }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Nondeterministic choice from the frontier; both cases are always
\* available so weak fairness drives progress.
ExploreFLB ==
  /\ pc = "running"
  /\ \E x \in frontier :
       \/ /\ x \notin marked
          /\ marked' = marked \cup {x}
          /\ frontier' = frontier \cup Succ[x]
       \/ /\ x \in marked
          /\ frontier' = frontier \ {x}
  /\ pc' = "running"

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == ExploreFLB \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ExploreFLB)

\* Invariant (1): every successor of a marked node is in the marked set or
\* the frontier -- the two sets together do not lose any reachable node.
Inv1 == MarkedSucs \subseteq (marked \cup frontier)

\* Invariant (2): the union of the marked set and the nodes reachable
\* from the frontier equals the nodes reachable from the union of both.
Inv2 == (marked \cup FrontierSucs) = TotalReachable

\* Invariant (3): the reachable set from the root equals the marked set plus
\* nodes reachable from the frontier.
Inv3 == TotalReachable = marked \cup FrontierSucs

PartialCorrectness == TotalReachable = marked

Termination == TotalReachable # Nodes => <>(pc = "done")

====