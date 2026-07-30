---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

\* Misra's variant of BFS: the visited (marked) set and the frontier may
\* overlap, which is what simplifies a parallel implementation.
\* The spec follows the description and all identifiers required by the .cfg.

CONSTANTS Nodes, Root, Succ, Seq

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

\* One action with two nondeterministic cases on a frontier node: add its
\* successors to the frontier and mark it, or drop it if already marked.  The
\* frontier is never emptied by marking, so it may overlap with marked.
Step ==
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

\* Safety: every successor of a marked node is already marked or still in the
\* frontier, so the frontier carries exactly the frontier of the reachable set.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup frontier) \subseteq
          {n \in Nodes : \E k \in marked \cup frontier : n \in SuccStar[k]}

Inv3 == {n \in Nodes : n \in SuccStar[Root]} \subseteq (marked \cup
          {n \in Nodes : n \in SuccStar[frontier]})

PartialCorrectness == {n \in Nodes : n \in SuccStar[Root]} = marked

Termination == (marked \cup frontier) # Nodes => (pc = "done")

====