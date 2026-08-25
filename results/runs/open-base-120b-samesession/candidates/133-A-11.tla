---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\* Concrete model parameters
\* ----------------------------------------------------------------------
NodeSet == {"n1", "n2", "n3", "n4"}
ASSUME Nodes = NodeSet

Root == "n1"

ProcSet == {"p1", "p2"}
ASSUME Procs = ProcSet

\* ----------------------------------------------------------------------
\* Concrete successor relation (each node has exactly two successors)
\* ----------------------------------------------------------------------
SuccMap == [
    "n1" |-> {"n2", "n3"},
    "n2" |-> {"n3", "n4"},
    "n3" |-> {"n4", "n1"},
    "n4" |-> {"n1", "n2"}
]

Succ == SuccMap

\* ----------------------------------------------------------------------
\* Operator that will be substituted for Succ in the parallel algorithm
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == SuccMap[n]

\* ----------------------------------------------------------------------
\* Bounded sequence operator (finite version of Seq)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Import the parallel reachability algorithm, overriding the needed
\* operators with the concrete definitions above.
\* ----------------------------------------------------------------------
INSTANCE ParReachAlg WITH
    Succ <- ConnectedToSomeButNotAll,
    Seq  <- LimitedSeq

\* ----------------------------------------------------------------------
\* Specification, invariant and property required by the .cfg file
\* ----------------------------------------------------------------------
Spec == ParReachAlg!Spec
Inv  == ParReachAlg!Inv
Refines == ParReachAlg!Refines

============================================================================