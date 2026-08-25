---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ

\* Concrete configuration values
Nodes == 1..4
Root  == 1
Procs == 1..2

\* ----------------------------------------------------------------------
\* Graph definition (each node has exactly two successors)
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == 
    [ n \in Nodes |-> 
        CASE n = 1 -> {2,3}
        [] n = 2 -> {3,4}
        [] n = 3 -> {4,1}
        [] OTHER  -> {1,2} ]

\* The constant Succ will be overridden by the .cfg with ConnectedToSomeButNotAll,
\* but we give it a definition here for completeness.
Succ == ConnectedToSomeButNotAll

\* ----------------------------------------------------------------------
\* Bounded sequence operator used by the .cfg
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the parallel algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel

vars == << marked, frontier, pc, sel >>

\* ----------------------------------------------------------------------
\* Initial state (concrete instantiation)
\* ----------------------------------------------------------------------
Init ==
    /\ marked   = {Root}
    /\ frontier = {Root}
    /\ pc       = [p \in Procs |-> 0]
    /\ sel      = [p \in Procs |-> Root]

\* ----------------------------------------------------------------------
\* Helper to nondeterministically pick a node from the frontier
\* ----------------------------------------------------------------------
PickNode == CHOOSE n \in frontier : TRUE

\* ----------------------------------------------------------------------
\* Actions for a single worker process p
\* ----------------------------------------------------------------------
ChooseNode(p) ==
    /\ p \in Procs
    /\ pc[p] = 0
    /\ LET n == PickNode IN
         sel' = [sel EXCEPT ![p] = n]
         pc'  = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED << marked, frontier >>

MarkNode(p) ==
    /\ p \in Procs
    /\ pc[p] = 1
    /\ n == sel[p]
    /\ marked'   = marked \cup {n}
    /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
    /\ pc'       = [pc EXCEPT ![p] = 2]
    /\ UNCHANGED sel

Done(p) ==
    /\ p \in Procs
    /\ pc[p] = 2
    /\ pc' = [pc EXCEPT ![p] = 0]
    /\ UNCHANGED << marked, frontier, sel >>

Next ==
    \E p \in Procs: ChooseNode(p) \/ MarkNode(p) \/ Done(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant (type correctness and control‑flow properties)
\* ----------------------------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs: pc[p] \in 0..2

\* ----------------------------------------------------------------------
\* Reachability predicate (used for the refinement property)
\* ----------------------------------------------------------------------
RECURSIVE Reachable(_,_)
Reachable(x, y) ==
    y \in ConnectedToSomeButNotAll[x] \/
    \E z \in Nodes: z \in ConnectedToSomeButNotAll[x] /\ Reachable(z, y)

\* ----------------------------------------------------------------------
\* Refinement property: every node reachable from the root is eventually marked
\* ----------------------------------------------------------------------
Refines == \A n \in Nodes: Reachable(Root, n) => <> (n \in marked)

====