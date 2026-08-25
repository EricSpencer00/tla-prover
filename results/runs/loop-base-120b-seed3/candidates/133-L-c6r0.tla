---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, ParReach

CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\*  Bounded sequence operator used in place of the unrestricted Seq.
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Concrete successor relation: each node has exactly two successors.
\*  The configuration substitutes ConnectedToSomeButNotAll for Succ.
\* ----------------------------------------------------------------------
CONSTANT SuccMap
ASSUME SuccMap \in [Nodes -> SUBSET Nodes] /\ 
       \A n \in Nodes : Cardinality(SuccMap[n]) = 2

ConnectedToSomeButNotAll(n) == SuccMap[n]

\* ----------------------------------------------------------------------
\*  Specification, invariant and refinement property inherited from the
\*  parallel reachability algorithm.
\* ----------------------------------------------------------------------
Spec     == ParReach!Spec
Inv      == ParReach!Inv
Refines  == ParReach!Refines

=============================================================================