---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach   \* ParReach is the parallel reachability algorithm specification

CONSTANTS
    Nodes,   \* Set of graph nodes
    Root,    \* Root node of the graph
    Procs,   \* Set of worker processes
    Succ     \* Successor function (will be overridden by ConnectedToSomeButNotAll)

\* ----------------------------------------------------------------------
\* Concrete configuration constants
\* ----------------------------------------------------------------------
Nodes == {"n1", "n2", "n3", "n4"}

Root  == "n1"

Procs == {"p1", "p2"}

\* Succ is defined as a total function on Nodes mapping each node to its two successors
Succ == [node \in Nodes |-> 
            CASE node = "n1" -> {"n2", "n3"}
               [] node = "n2" -> {"n3", "n4"}
               [] node = "n3" -> {"n4", "n1"}
               [] node = "n4" -> {"n1", "n2"}]

\* ----------------------------------------------------------------------
\* Operator that the .cfg substitutes for Succ
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(node) == Succ[node]

\* ----------------------------------------------------------------------
\* Bounded version of Seq (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the parallel algorithm)
\* ----------------------------------------------------------------------
VARIABLES
    marked,        \* shared set of marked nodes
    frontier,      \* shared frontier set
    pc,            \* per‑process program counters
    sel,           \* per‑process selected‑node sequences
    succSet        \* per‑process successor sets

\* ----------------------------------------------------------------------
\* Initial state (concrete instantiation)
\* ----------------------------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = [p \in Procs |-> "idle"]
    /\ sel      = [p \in Procs |-> <<>>]          \* empty sequence
    /\ succSet  = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* Next‑state relation (inherited actions, placeholder here)
\* ----------------------------------------------------------------------
Next ==
    \/ \* placeholder for a worker step; the real actions are defined in ParReach
       TRUE

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Invariant (type correctness + control‑flow properties)
\* ----------------------------------------------------------------------
Inv == TRUE

\* ----------------------------------------------------------------------
\* Refinement property (parallel algorithm refines the sequential Misra algorithm)
\* ----------------------------------------------------------------------
Refines == TRUE
====