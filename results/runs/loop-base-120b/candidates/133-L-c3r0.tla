---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS 
    Nodes,      \* the finite set of graph nodes (|Nodes| = 4)
    Root,       \* the distinguished start node
    Procs,      \* the set of worker processes (|Procs| = 2)
    Succ        \* (will be overridden by the .cfg with ConnectedToSomeButNotAll)

\* ----------------------------------------------------------------------
\*  Bounded successor relation used for model checking.
\*  Each node must have exactly two distinct successors different from itself.
\*  The .cfg substitutes this operator for the abstract Succ operator.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    CHOOSE S \in SUBSET Nodes :
        /\ Cardinality(S) = 2
        /\ n \notin S

\* ----------------------------------------------------------------------
\*  Finite version of the sequence operator.  The .cfg replaces the
\*  standard Seq operator with this definition to keep the state space
\*  finite (sequences are bounded by the number of nodes).
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Specification, invariants and refinement property.
\*  All behavioural definitions are inherited from the parallel
\*  reachability algorithm (module ParReach).  We simply expose the
\*  relevant operators under the names required by the .cfg file.
\* ----------------------------------------------------------------------
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====