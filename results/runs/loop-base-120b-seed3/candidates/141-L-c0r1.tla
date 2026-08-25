---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Main actions (choose a node from the frontier)
\* ----------------------------------------------------------------------
ChooseAction ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = pc

\* ----------------------------------------------------------------------
\* Termination action
\* ----------------------------------------------------------------------
TerminateAction ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Next == ChooseAction \/ TerminateAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(ChooseAction)

\* ----------------------------------------------------------------------
\* Reachability operator (transitive closure of Succ)
\* ----------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE
        LET NextSet == { y \in Nodes : \E x \in S : y \in Succ[x] }
        IN S \cup Reach(NextSet)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is in marked or frontier
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
\* ----------------------------------------------------------------------
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked = Reach({Root})
\* ----------------------------------------------------------------------
PartialCorrectness ==
    (pc = "done") => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

====