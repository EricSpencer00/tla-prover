---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, ParReach

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

=============================================================================