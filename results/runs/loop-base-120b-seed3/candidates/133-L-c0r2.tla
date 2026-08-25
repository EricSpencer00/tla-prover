---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS
    Nodes,
    Root,
    Procs,
    Succ

\* ----------------------------------------------------------------------
\* Operator that the .cfg substitutes for Succ
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(node) == Succ[node]

\* ----------------------------------------------------------------------
\* Bounded version of Seq (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====