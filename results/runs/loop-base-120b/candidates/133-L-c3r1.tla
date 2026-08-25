---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

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

====