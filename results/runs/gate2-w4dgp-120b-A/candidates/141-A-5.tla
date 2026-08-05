---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Misra's algorithm for reachable nodes: a BFS-like exploration in which the
\* marked set and the frontier set may overlap (unusual, but makes parallel
\* implementation easier). The invariants establish partial correctness even
\* though overlap would break a standard BFS proof.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Marked == {n \in Nodes : marked[n]}
ReachableFromFrontier ==
  {y \in Nodes : \E x \in frontier : y \in Succ[x]}

Init == /\ marked = [n \in Nodes |-> FALSE]
        /\ frontier = {Root}
        /\ pc = 0

CheckNode == \E x \in frontier :
               /\ marked' = [marked EXCEPT ![x] = TRUE]
               /\ frontier' = frontier \cup Succ[x]
               /\ pc' = (pc + 1) % 2

DiscardNode == \E x \in frontier :
                 /\ marked[x]
                 /\ frontier' = frontier \ {x}
                 /\ pc' = (pc + 1) % 2

Next == CheckNode \/ DiscardNode

Terminating == frontier = {}

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CheckNode) /\ WF_vars(DiscardNode)
        /\ (Terminating => \A n \in Nodes : marked[n] \/ n \in frontier)
        /\ (Terminating => \A n \in Nodes : frontier[n] => marked[n])

TypeOK == /\ marked \in [Nodes -> BOOLEAN]
          /\ frontier \subseteq Nodes

Inv1 == \A x \in Nodes : marked[x] => (Succ[x] \subseteq Marked \cup frontier)

Inv2 == (Marked \cup ReachableFromFrontier)
          = {n \in Nodes :
               \E x \in Marked \cup frontier : n \in Succ[x] \cup {x}}

Inv3 == {n \in Nodes :
            \E x \in Marked \cup frontier : n \in Succ[x] \cup {x}} = Marked

PartialCorrectness == (\A n \in Nodes : marked[n]) => Marked = {n \in Nodes : TRUE}

Termination == Terminating ~> Terminating

INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
properties == Termination
====