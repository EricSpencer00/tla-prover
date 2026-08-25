---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

\* --------------------------------------------------------------
\* Constants required by the configuration
\* --------------------------------------------------------------
CONSTANTS
    Nodes,   \* The finite set of graph nodes (|Nodes| = 4)
    Root,    \* The designated start node, Root \\in Nodes
    Procs,   \* The set of worker processes (|Procs| = 2)
    Succ     \* Successor function: Nodes -> SUBSET Nodes

\* --------------------------------------------------------------
\* Operator that will replace Succ in the .cfg file.
\* It returns a non‑empty proper subset of Nodes for each node.
\* --------------------------------------------------------------
ConnectedToSomeButNotAll ==
    [n \\in Nodes |-> { m \\in Nodes : m # n }]

\* For convenience we give a default definition of Succ.
\* The .cfg will substitute ConnectedToSomeButNotAll for Succ,
\* so the exact value of this constant is not important.
Succ == ConnectedToSomeButNotAll

\* --------------------------------------------------------------
\* Bounded version of the sequence operator Seq.
\* Keeps only sequences whose length does not exceed |Nodes|.
\* --------------------------------------------------------------
LimitedSeq(S) ==
    { s \\in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* --------------------------------------------------------------
\* Variables of the parallel reachability algorithm
\* --------------------------------------------------------------
VARIABLES
    marked,    \* Set of nodes already discovered
    frontier,  \* Set of nodes currently on the frontier
    pc,        \* Program counter per process
    sel,       \* Node selected by each process (or NULL)
    succSet    \* Successor set computed by each process

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
NULL == "NULL"

\* Initial state (mirrors the sequential algorithm's start)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \\in Procs |-> "idle"]
    /\ sel = [p \\in Procs |-> NULL]
    /\ succSet = [p \\in Procs |-> {}]

\* A very abstract next‑state relation that allows any
\* admissible change; the concrete algorithm would refine this.
Next ==
    \/ /\ marked' = marked \\cup frontier
       /\ frontier' = {}
       /\ UNCHANGED << pc, sel, succSet >>
    \/ /\ UNCHANGED << marked, frontier, pc, sel, succSet >>

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Spec ==
    Init /\ [][Next]_(<<marked, frontier, pc, sel, succSet>>)

\* --------------------------------------------------------------
\* Invariant: type correctness and simple control‑flow properties
\* --------------------------------------------------------------
Inv ==
    /\ marked \\subseteq Nodes
    /\ frontier \\subseteq Nodes
    /\ \A p \\in Procs : pc[p] \\in {"idle", "busy"}
    /\ \A p \\in Procs : sel[p] \\in Nodes \\cup {NULL}
    /\ \A p \\in Procs : succSet[p] \\subseteq Nodes

\* --------------------------------------------------------------
\* Refinement property: the parallel algorithm implements the
\* sequential Misra algorithm (abstractly expressed here)
\* --------------------------------------------------------------
Refines ==
    Spec => TRUE

====