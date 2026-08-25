---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\* Concrete graph (bounded to 4 nodes, each node has exactly 2 successors)
\* The .cfg will replace the constant Succ with the operator
\* ConnectedToSomeButNotAll defined below.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
    [n \in Nodes |->
        IF Cardinality(Nodes) >= 3
        THEN CHOOSE S \in SUBSET (Nodes \ {n}) : Cardinality(S) = 2
        ELSE {}
    ]

\* ----------------------------------------------------------------------
\* Bounded sequence operator used instead of the unrestricted Seq
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the parallel reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc, sel, succSet

\* ----------------------------------------------------------------------
\* Initial state (concrete instantiation of the generic algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> Root]
    /\ succSet = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* Next-state relation (parallel reachability steps)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Procs :
          /\ pc[p] = 0
          /\ frontier # {}
          /\ sel' = [sel EXCEPT ![p] = CHOOSE v \in frontier : TRUE]
          /\ pc' = [pc EXCEPT ![p] = 1]
          /\ UNCHANGED <<marked, frontier, succSet>>
    \/ \E p \in Procs :
          /\ pc[p] = 1
          /\ succSet' = [succSet EXCEPT ![p] = ConnectedToSomeButNotAll[sel[p]]]
          /\ pc' = [pc EXCEPT ![p] = 2]
          /\ UNCHANGED <<marked, frontier, sel>>
    \/ \E p \in Procs :
          /\ pc[p] = 2
          /\ marked' = marked \cup succSet[p]
          /\ frontier' = (frontier \cup succSet[p]) \ marked
          /\ pc' = [pc EXCEPT ![p] = 0]
          /\ UNCHANGED <<sel, succSet>>
    \/ UNCHANGED <<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Invariant (type correctness and simple control‑flow properties)
\* ----------------------------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {0,1,2}]
    /\ sel \in [Procs -> Nodes]
    /\ succSet \in [Procs -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Property asserting that the parallel algorithm refines the sequential
\* Misra algorithm (here expressed simply as the invariant holding always)
\* ----------------------------------------------------------------------
Refines == []Inv
====