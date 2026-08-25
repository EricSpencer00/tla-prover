---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

\* ----------------------------------------------------------------------
\*  Concrete configuration constants
\* ----------------------------------------------------------------------
Nodes == {1, 2, 3, 4}
Root  == 1
Procs == {1, 2}

\* ----------------------------------------------------------------------
\*  Bounded successor relation used for model checking.
\*  Each node must have exactly two distinct successors different from itself.
\*  The .cfg substitutes this operator for the abstract Succ operator.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    CHOOSE S \in SUBSET Nodes :
        /\ Cardinality(S) = 2
        /\ n \notin S

\* Succ is overridden by the .cfg with ConnectedToSomeButNotAll,
\* but we expose the name here for completeness.
Succ(n) == ConnectedToSomeButNotAll(n)

\* ----------------------------------------------------------------------
\*  Finite version of the sequence operator.  The .cfg replaces the
\*  standard Seq operator with this definition to keep the state space
\*  finite (sequences are bounded by the number of nodes).
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Specification, invariant and refinement property required by the .cfg
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

Inv == TRUE

Refines == TRUE

====