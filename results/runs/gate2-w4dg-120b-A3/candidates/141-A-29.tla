---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

(* The frontier and the marked set may overlap; that is what avoids having to
   remove a node from the frontier before it is visited, which is the point of
   Misra's variant. *)

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

\* One main action with two cases, chosen nondeterministically from the frontier.
Explore ==
  /\ \E n \in frontier :
       \/ /\ n \notin marked
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
            /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_vars

\* Every successor of a visited node is either already visited or waiting in the
\* frontier: nothing reachable is lost to an ordering quirk of the overlap.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The frontier's reachable region is closed under Succ, so no reachable node is
\* stranded outside both marked and frontier.
Inv2 == (marked \cup frontier) \cup (Succ[marked \cup frontier]) = marked \cup (Succ[frontier] \cup frontier)

\* Reachable-from-the-root is the disjoint union of visited and frontier-reachable.
Inv3 == ReachableFromRoot == marked \cup (Succ[frontier] \cup frontier)

PartialCorrectness == pc = "done" => marked = ReachableFromRoot

Termination == (FrontierBounded => (pc = "running") ~> (pc = "done"))

\* Operators expected by, and overridden in, the .cfg file.
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Sequences.Seq, overridden in the .cfg file.
LimitedSeq(S) == CHOOSE s \in Seq(S) : \A t \in Seq(S) : Len(t) <= Len(s)

====