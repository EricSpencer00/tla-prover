---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS
    Nodes,   \* Set of graph nodes (finite)
    Root,    \* Distinguished root node
    Procs,   \* Set of worker processes
    Succ,    \* Graph successor relation: [Nodes -> SUBSET Nodes]
    Seq      \* Upper bound on the length of any sequence (used for bounded overrides)

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
NodeSeq == 1..Seq  \* Index set for bounded sequences

\* ----------------------------------------------------------------------
\* Types (used in the inductive invariant)
\* ----------------------------------------------------------------------
NodeSet == SUBSET Nodes
NodeSeqSet == SUBSET NodeSeq

\* ----------------------------------------------------------------------
\* State variables inherited from the parallel algorithm
\* ----------------------------------------------------------------------
VARIABLES
    marked,          \* Nodes that have been discovered
    frontier,        \* Nodes currently being explored
    pc,              \* Program counter per process (set of control locations)
    work,            \* Selected node per process (or "None")
    succSet          \* Successor set per process (bounded to Seq elements)

\* ----------------------------------------------------------------------
\* Types for per-process variables
\* ----------------------------------------------------------------------
PCVals == {"Init", "Select", "Explore", "Done"}   \* Example control locations

\* ----------------------------------------------------------------------
\* Helper to bound sequences (override of finite maps)
\* ----------------------------------------------------------------------
BoundedSeq(ovr) ==
    [i \in NodeSeq |-> IF i \in DOMAIN ovr THEN ovr[i] ELSE {}]

\* ----------------------------------------------------------------------
\* Initial state (inherits behavior of the parallel algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Init"]
    /\ work = [p \in Procs |-> "None"]
    /\ succSet = [p \in Procs |-> <<>>]   \* empty sequence of successors

\* ----------------------------------------------------------------------
\* Actions (inherits from the parallel algorithm, simplified)
\* ----------------------------------------------------------------------
Select ==
    \E p \in Procs :
        /\ pc[p] = "Init"
        /\ work' = [work EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
        /\ pc' = [pc EXCEPT ![p] = "Explore"]
        /\ UNCHANGED <<marked, frontier, succSet>>

Explore ==
    \E p \in Procs :
        /\ pc[p] = "Explore"
        /\ work[p] # "None"
        /\ let n == work[p] in
           /\ succSet' = [succSet EXCEPT ![p] = BoundedSeq({i \in 1..Seq |-> Succ[n][i]})]
           /\ marked' = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup Succ[n]
           /\ work' = [work EXCEPT ![p] = "None"]
           /\ pc' = [pc EXCEPT ![p] = "Done"]
        /\ UNCHANGED <<>>

Done ==
    \E p \in Procs :
        /\ pc[p] = "Done"
        /\ pc' = [pc EXCEPT ![p] = "Init"]
        /\ UNCHANGED <<marked, frontier, work, succSet>>

Next ==
    \/ Select
    \/ Explore
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, work, succSet>>

\* ----------------------------------------------------------------------
\* Inductive invariant (type correctness + control‑flow properties)
\* ----------------------------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> PCVals]
    /\ work \in [Procs -> {"None"} \cup Nodes]
    /\ succSet \in [Procs -> Seq -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Refinement property: the parallel algorithm implements the sequential Misra algorithm
\* (simplified version asserting that the set of marked nodes never exceeds the
\*   nodes reachable from the root in the underlying graph)
\* ----------------------------------------------------------------------
ReachableFromRoot ==
    RECURSIVE Reach(_)
    Reach(s) ==
        IF s = {} THEN {}
        ELSE LET n == CHOOSE x \in s : TRUE IN
             {n} \cup Reach({m \in Nodes : m \in Succ[n]})
    IN Reach({Root})

Refines == marked \subseteq ReachableFromRoot

\* ----------------------------------------------------------------------
\* THEOREM (optional, not exported)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====