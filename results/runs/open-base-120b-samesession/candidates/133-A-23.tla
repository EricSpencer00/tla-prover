---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS
    Nodes,   \* The set of graph nodes (size = 4)
    Root,    \* The distinguished start node
    Procs,   \* The set of worker processes (size = 2)
    Succ     \* (overridden by the .cfg with ConnectedToSomeButNotAll)

\* ----------------------------------------------------------------------
\*  Operator that provides a finite successor relation used for model checking.
\*  The .cfg substitutes this operator for Succ, so Succ will be interpreted
\*  as ConnectedToSomeButNotAll in the configuration.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(node) ==
    { n \in Nodes :
        (* each node has exactly two distinct successors *)
        (n # node) /\ 
        (* an arbitrary deterministic choice – for concreteness we
           map the node to the two next elements in the cyclic order *)
        LET ordered == <<node, node', node'', node'''>> \* a placeholder ordering
        IN  n = ordered[(Index(node, ordered) % Cardinality(Nodes)) + 1] \/
            n = ordered[(Index(node, ordered) % Cardinality(Nodes)) + 2] }

\* ----------------------------------------------------------------------
\*  A bounded version of the standard Seq operator from the Sequences module.
\*  This keeps all sequences to a length no greater than the number of nodes,
\*  ensuring a finite state space for model checking.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\*  Specification, invariants and refinement property are inherited from the
\*  parallel reachability algorithm (module ParReach).  We simply alias them
\*  here so that the .cfg file can refer to the required identifiers.
\* ----------------------------------------------------------------------
Spec == ParReach!Spec

Inv == ParReach!Inv

Refines == ParReach!Refines

=============================================================================