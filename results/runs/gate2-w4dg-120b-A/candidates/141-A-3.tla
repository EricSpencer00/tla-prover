---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* marked: visited nodes (the output of the algorithm); frontier: nodes yet
\* to be fully explored, overlapping with marked; pc: the loop/termination state.
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

\* Process a frontier node chosen nondeterministically. If not yet marked, add it
\* and all its successors to the frontier; otherwise remove it.
Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ(n)
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore(Root))

\* Partial correctness is carried by three complementary invariants.
Inv1 == \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Inv2 == ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Terminated == pc = "done"

====