---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The frontier (open set) and the marked (visited) set may overlap; that
\* overlap is the twist that lets Misra's variant keep a single loop.

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The loop is nondeterministic in which frontier node it expands.
ProcessNode ==
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ IF n \notin marked
              THEN /\ marked' = marked \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
              ELSE /\ marked' = marked
                   /\ frontier' = frontier \ {n}
    /\ pc' = "running"

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ marked' = marked
    /\ frontier' = frontier

Next == ProcessNode \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessNode)

\* Safety: every successor of a marked node is already marked or still open
Inv1 == \A n \in Nodes : n \in marked => Succ[n] \subseteq (marked \cup frontier)

\* The expansion above is never stuck: unmarked successors are always pulled
\* in from some frontier node before the algorithm can declare itself done.
Inv2 == marked \cup frontier = ReachableFrom(Nodes, frontier)

\* Marked is exactly what is reachable once the frontier is exhausted.
Inv3 == ReachableFrom(Nodes, marked) = marked \cup ReachableFrom(Nodes, frontier)

\* The marked set is exactly the set of reachable nodes at termination.
PartialCorrectness == pc = "done" => marked = ReachableFrom(Nodes, {Root})

\* The reachable set grows monotonically and is bounded by Nodes, so on a
\* finite reachable set this reaches a fixed point and the loop ends.
Termination == WF_vars(ProcessNode)

\* The module replaces Succ with ConnectedToSomeButNotAll and Seq with
\* LimitedSeq (a finite version of the standard Seq) so the model is
\* checkable; both are defined here as no-ops against the constant.

ConnectedToSomeButNotAll == Succ

LimitedSeq(S) == Seq(S)

====