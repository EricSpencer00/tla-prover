---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

\* -----------------------------------------------------------------
\* Constants required by the configuration
\* -----------------------------------------------------------------
CONSTANTS
    Nodes,   \* the finite set of graph nodes
    Root,    \* the distinguished start node (Root \\in Nodes)
    Procs,   \* the set of worker processes
    Succ     \* (will be overridden by ConnectedToSomeButNotAll)

\* -----------------------------------------------------------------
\* Bounded version of Seq (replaces Seq from the Sequences module)
\* -----------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* -----------------------------------------------------------------
\* Concrete successor relation used for model checking.
\* The .cfg substitutes this operator for Succ.
\* Each node is connected to some (but not all) other nodes;
\* for the purpose of the model we give a simple definition that
\* guarantees at least one and at most |Nodes|-1 successors.
\* -----------------------------------------------------------------
ConnectedToSomeButNotAll ==
    [ n \in Nodes |-> 
        { m \in Nodes : m # n } ]

\* -----------------------------------------------------------------
\* Specification, invariant and refinement property.
\* All dynamic behaviour (Init, Next, etc.) is inherited from the
\* parallel reachability algorithm module ParReach.
\* -----------------------------------------------------------------
Spec == ParReachSpec

Inv == ParReachInv

Refines == ParReachRefines

=============================================================================