---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, GraphLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions (taken from the extended modules)
\* ----------------------------------------------------------------------
(* Assume the extended modules provide:
   - Succ : [Nodes -> SUBSET Nodes]   the successor relation
   - ReachableFrom(S) : SUBSET Nodes   the set of nodes reachable from a set S
*)

\* ----------------------------------------------------------------------
\* State space
\* ----------------------------------------------------------------------
vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Step action: pick a node from the frontier, mark it,
\* and add its unmarked successors to the frontier
\* ----------------------------------------------------------------------
Step ==
    /\ pc = "Run"
    /\ \E n \in frontier :
        LET succ == Succ[n] IN
        /\ marked'   = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (succ \ marked)
        /\ pc'       = IF frontier' = {} THEN "Done" ELSE "Run"

\* ----------------------------------------------------------------------
\* Stuttering action after termination
\* ----------------------------------------------------------------------
Done ==
    /\ pc = "Done"
    /\ marked'   = marked
    /\ frontier' = frontier
    /\ pc'       = "Done"

Next == Step \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and closure of successors
\* ----------------------------------------------------------------------
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
\* ----------------------------------------------------------------------
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* Property: when the algorithm terminates, marked equals the reachable set
\* ----------------------------------------------------------------------
TerminationProp ==
    (pc = "Done") => (marked = ReachableFrom({Root}))

PROPERTIES == TerminationProp

====