---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS
    Nodes,   \* the set of graph nodes (4 elements)
    Root,    \* the designated start node
    Procs,   \* the set of worker processes (2 elements)
    Succ     \* (will be overridden by ConnectedToSomeButNotAll by the .cfg)

\* ----------------------------------------------------------------------
\*  Operator that supplies a bounded successor relation.
\*  Each node has exactly two successors taken from Nodes.
\*  The .cfg replaces every occurrence of the constant Succ with this
\*  operator.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    /\ n \in Nodes
    /\ CASE n = n1 -> {n2, n3}
        [] n = n2 -> {n3, n4}
        [] n = n3 -> {n4, n1}
        [] n = n4 -> {n1, n2}
        [] OTHER  -> {}

\* ----------------------------------------------------------------------
\*  Limited version of Seq for model checking.
\*  Sequences over any set S whose length does not exceed |Nodes|.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Specification, invariants and refinement property.
\*  They are simply aliased to the definitions in the parallel
\*  reachability algorithm module (ParReach).
\* ----------------------------------------------------------------------
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====