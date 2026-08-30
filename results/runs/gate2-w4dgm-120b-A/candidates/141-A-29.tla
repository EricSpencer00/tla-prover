---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* Misra's variant of BFS: the marked and frontier sets may overlap, which is
\* what makes the algorithm parallel-friendly. It is modeled as a single
\* sequential process exploring a directed graph from a root node.
CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* ReachableFrom(t) is the set of nodes reachable from a set t via graph edges.
ReachableFrom(t) ==
    LET R[S \in SUBSET Nodes] ==
        IF S = {} THEN {}
        ELSE LET x == CHOOSE e \in S : TRUE
                 succs == ConnectedToSomeButNotAll[x]
             IN succs \cup R[S \ {x}]
    IN R[t]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The main action has two nondeterministic cases, chosen from the frontier:
\* mark a node and add its successors to the frontier, or drop an already-
\* marked node from the frontier. Either way the frontier shrinks or grows
\* but never gets stuck with a reachable node forever.
Explore(n) ==
    /\ n \in frontier
    /\ \E m \in {"running", "done"} : pc' = m
    /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in frontier : Explore(n)) \/ Terminate

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E n \in frontier : Explore(n))
    /\ WF_vars(Terminate)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

\* Invariant 1: every successor of a marked node is in the marked set or the
\* frontier, so no reachable node is ever lost from the two sets.
Inv1 ==
    \A x \in Nodes : (x \in marked) => (ConnectedToSomeButNotAll[x] \subseteq (marked \cup frontier))

\* Two-part subdivision of reachability: the reachable-from-union set equals
\* the reachable-from-marked union reachable-from-frontier sets.
Inv2 ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* Exact coverage: the reachable-from-root set is marked nodes plus nodes
\* reachable from the frontier, with no reachable node left out.
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

\* If the reachable set is finite, the algorithm cannot run forever drifting
\* around it: the frontier eventually runs empty and the process terminates.
Termination ==
    \A f \in [Nat -> Nodes] :
        (\A i \in Nat : f[i] \in ReachableFrom({Root}))
            => <>(frontier = {})

====