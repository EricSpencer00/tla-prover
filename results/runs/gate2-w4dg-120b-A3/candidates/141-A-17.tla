---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* The full graph is given by the Succ relation. The .cfg swaps in a
\* bounded version of it (via ConnectedToSomeButNotAll) when the model
\* is checked, so we model Succ abstractly here.
CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

FrontierSpace == UNION {Succ[n] : n \in frontier}

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* What the algorithm has actually covered: the marked nodes plus
\* whatever is still reachable through the frontier.
ReachableFromFrontier ==
  LET Extend(S, F) ==
        IF F = {} THEN S
        ELSE LET x == CHOOSE n \in F : TRUE IN Extend(S \cup Succ[x], F \ {x})
  IN Extend(visited, frontier)

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The two cases of the main action: either absorb a new node and
\* spread its successors into the frontier, or drop an already-marked
\* node from the frontier.
Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       IF n \notin visited
         THEN /\ visited' = visited \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ visited' = visited
              /\ frontier' = frontier \ {n}
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)
        /\ WF_vars(Terminate)

\* Because frontier may overlap visited, reachable nodes can sit in
\* either set, which is what these invariants track.
Inv1 == FrontierSpace \subseteq (visited \cup frontier)
Inv2 == visited \cup ReachableFromFrontier = ReachableFromFrontier
Inv3 == (Nodes \ visited) \subseteq ReachableFromFrontier

PartialCorrectness == visited = ReachableFromFrontier

Termination == pc = "done"

\* The .cfg swaps in a bounded version of Succ for the model, and
\* replaces the standard Seq with a finite version.
ConnectedToSomeButNotAll == TRUE
LimitedSeq == TRUE

====