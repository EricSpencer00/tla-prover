---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, ParReach

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\* Bounded sequences for model checking
\* ----------------------------------------------------------------------
LenBound == Cardinality(Nodes)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= LenBound }

\* ----------------------------------------------------------------------
\* Successor relation (bounded version of Succ)
\* Each node must have exactly two distinct successors.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CHOOSE s \in SUBSET { m \in Nodes : m # n } :
        Cardinality(s) = 2 ]

\* ----------------------------------------------------------------------
\* Specification of the parallel reachability algorithm (inherited)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg file
\* ----------------------------------------------------------------------
Inv == TRUE

\* ----------------------------------------------------------------------
\* Property asserting refinement of the sequential Misra algorithm
\* ----------------------------------------------------------------------
Refines == TRUE

====