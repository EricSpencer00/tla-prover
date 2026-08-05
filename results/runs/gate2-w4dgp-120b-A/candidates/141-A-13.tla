---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* LimitedSeq is injected into the module by operator override from the .cfg,
\* which replaces the unbounded Seq from Sequences with a FINITE version
\* that has the same name but a built-in bound. It is defined here as a
\* RENAMED operator so the override is well-formed syntactically.
LimitedSeq == Seq

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "exploring"

\* Misra's BFS variant: the frontier may overlap marked, so a visited node can
\* be picked again. The action is chosen for any frontier node, which is why
\* fairness on the whole action is sufficient for termination.
Explore ==
  /\ pc = "exploring"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ IF x \notin marked
            THEN /\ marked' = marked \cup {x}
                 /\ frontier' = frontier \cup Succ[x]
            ELSE /\ frontier' = frontier \ {x}
                 /\ marked' = marked
  /\ pc' = "exploring"

Done == /\ frontier = {} /\ pc = "exploring" /\ pc' = "done" /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* Every successor of a marked node has been discovered into marked or frontier.
Inv1 == \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

\* The reachable-from-marked-or-frontier set is closed under taking successors.
Inv2 == {y \in Nodes : (\E x \in (marked \cup frontier) : y \in Succ[x])} = (marked \cup frontier)

\* Reachable from the root splits exactly into marked plus reachable-from-frontier.
Inv3 == {y \in Nodes : (\E x \in {Root} : y \in Succ[x])} = (marked \cup {y \in Nodes : (\E x \in frontier : y \in Succ[x])})

PartialCorrectness == pc = "done" => marked = {y \in Nodes : (\E x \in {Root} : y \in Succ[x])}

\* With a finite reachable set the frontier cannot linger forever: each loop
\* either adds a new element to the finite marked set or removes one from the frontier.
Termination == (frontier # {}) ~> (frontier = {})

Succ == {<<x, y>> \in Nodes \X Nodes : y \in Succ[x]}
====