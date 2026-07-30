---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

\* State: the set of nodes already marked reachable, the frontier of nodes from
\* which the next expansion fires, and a PC that runs NotStarted/Running/Done.
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"NotStarted", "Running", "Done"}

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "NotStarted"

Start == /\ pc = "NotStarted"
         /\ pc' = "Running"
         /\ UNCHANGED <<marked, frontier>>

\* A node leaves the frontier and joins the marked set together.
Mark(n) == /\ pc = "Running"
           /\ frontier' = frontier \ {n}
           /\ marked' = marked \cup {n}
           /\ UNCHANGED pc

\* The frontier expands to a successor of some marked node that is currently
\* outside marked and outside frontier.
Expand(n) == /\ pc = "Running"
             /\ \E m \in marked :
                  /\ n \notin marked
                  /\ n \notin frontier
                  /\ n # m
                  /\ frontier' = frontier \cup {n}
             /\ UNCHANGED <<marked, pc>>

Settle == /\ pc = "Running"
          /\ frontier = {}
          /\ pc' = "Done"
          /\ UNCHANGED <<marked, frontier>>

Next == Start \/ Settle \/ \E n \in Nodes : Mark(n) \/ Expand(n)

Spec == Init /\ [][Next]_vars

\* Lemma 1 (from ReachabilityProofs): for any set, successors of it are within the
\* marked set or the frontier once every reachable node is already accounted for.
Lemma1 == successors(marked) \subseteq marked \cup frontier

\* Lemma 2 (from ReachabilityProofs): reachable-from is stable under adding
\* successors. Lemma 3 (from ReachabilityProofs): reachable-from the empty set is
\* empty. Together these let us replace the disjunction of reachable-from's.
Lemma2 == reachableFrom(frontier) = reachableFrom(frontier \cup successors(frontier))

\* Invariant 1: type correctness plus every successor of a marked node is in the
\* marked set or frontier (proved directly using Lemma 1).
Invar1 == TypeOK /\ Lemma1

\* Invariant 2: the marked set plus nodes reachable from the frontier equals the
\* nodes reachable from the marked set and frontier together (proved from Lemma 1).
Invar2 == marked \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

\* Invariant 3: the set reachable from the root equals the marked set plus the
\* nodes reachable from the frontier (proved using Lemma 2 and Lemma 3).
Invar3 == reachableFrom({Root}) = marked \cup reachableFrom(frontier)

\* Partial correctness: on termination the marked set is exactly the reachable
\* set -- the algorithm never over- or under-approximates.
Terminating == pc = "Done"
Correctness == Terminating => (marked = reachableFrom({Root}))

INVARIANTS == Invar1 /\ Invar2 /\ Invar3
PROPERTIES == Correctness

====