---- MODULE MCParReach ----
EXTENDS FiniteSets, Sequences, Naturals

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS
    Nodes,   \* the set of graph nodes
    Root,    \* the distinguished start node
    Procs,   \* the set of worker processes
    Succ     \* (will be overridden by ConnectedToSomeButNotAll)

\*--------------------------------------------------------------------
\* Operator that supplies a concrete successor function.
\* The .cfg substitutes Succ with this operator.
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll == 
    [n \in Nodes |-> 
        IF n = Root          THEN { (Root + 1) % Cardinality(Nodes), (Root + 2) % Cardinality(Nodes) }
        ELSIF n = (Root + 1) % Cardinality(Nodes) THEN { (Root + 2) % Cardinality(Nodes), (Root + 3) % Cardinality(Nodes) }
        ELSIF n = (Root + 2) % Cardinality(Nodes) THEN { (Root + 3) % Cardinality(Nodes), Root }
        ELSE { Root, (Root + 1) % Cardinality(Nodes) }
    ]

\*--------------------------------------------------------------------
\* Finite version of Seq used for model checking.
\* The .cfg replaces Seq with LimitedSeq.
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* State variables (inherited from the parallel reachability algorithm)
\*--------------------------------------------------------------------
VARIABLES
    marked,      \* set of nodes already discovered
    frontier,    \* set of nodes to be explored next
    pc,          \* program counters per process
    sel,         \* selected node per process
    succSet      \* successor set per process

\*--------------------------------------------------------------------
\* Initial state (concrete instantiation of the abstract algorithm)
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> {}]
    /\ succSet = [p \in Procs |-> {}]

\*--------------------------------------------------------------------
\* Next-state relation (inherited from the parallel algorithm).
\* Here we give a placeholder that permits any state change respecting
\* type constraints – the real algorithm would be imported from the
\* parallel specification module.
\*--------------------------------------------------------------------
Next ==
    \/ \* Worker i performs a step (placeholder)
       \E i \in Procs :
          /\ pc' = [pc EXCEPT ![i] = "working"]
          /\ UNCHANGED << marked, frontier, sel, succSet >>
    \/ \* No-op (allows stuttering)
       /\ UNCHANGED << marked, frontier, pc, sel, succSet >>

\*--------------------------------------------------------------------
\* Specification formula required by the .cfg
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\*--------------------------------------------------------------------
\* Inductive invariant (type correctness)
\*--------------------------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs : sel[p] \subseteq Nodes
    /\ \A p \in Procs : succSet[p] \subseteq Nodes

\*--------------------------------------------------------------------
\* Refinement property (placeholder – actual property defined elsewhere)
\*--------------------------------------------------------------------
Refines == TRUE

====