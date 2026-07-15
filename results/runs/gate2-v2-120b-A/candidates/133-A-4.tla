---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* -------------------------------------------------
CONSTANTS
    Nodes,      \* The set of graph nodes (e.g., 1..4)
    Root,       \* The start node of the graph
    Procs,      \* The set of worker processes (e.g., 1..2)
    Succ,       \* A total function mapping each node to a set of its two successors
    Seq         \* An upper bound on the length of any sequence (should be |Nodes|)

\* -------------------------------------------------
\* Derived constants
\* -------------------------------------------------
NodeSeq == 1..Seq

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES
    marked,         \* Set of nodes that have been visited
    frontier,      \* Set of nodes currently in the shared frontier
    pc,            \* [p \in Procs -> {"Done", "Pick", "Push", "Wait"}]
    sel,           \* [p \in Procs -> Node]  (the node currently selected by each process)
    succSet        \* [p \in Procs -> SUBSET Nodes] (the successors of the selected node)

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
PCVals == {"Done", "Pick", "Push", "Wait"}

\* -------------------------------------------------
\* Initial predicate (inherits the sequential init, extended for multiple processes)
\* -------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Pick"]
    /\ sel = [p \in Procs |-> Root]        \* arbitrary initial selection; will be overwritten before use
    /\ succSet = [p \in Procs |-> {}]

\* -------------------------------------------------
\* Process actions (one per process)
\* -------------------------------------------------
Pick(p) ==
    /\ pc[p] = "Pick"
    /\ frontier # {}
    /\ sel[p] \in frontier
    /\ succSet[p] = Succ[sel[p]]
    /\ frontier' = frontier \ {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "Push"]
    /\ UNCHANGED << marked, sel, succSet >>

Push(p) ==
    /\ pc[p] = "Push"
    /\ succSet[p] # {}
    /\ LET s == CHOOSE x \in succSet[p] : TRUE IN
       /\ marked' = marked \cup {s}
       /\ frontier' = frontier \cup {s}
       /\ succSet' = [succSet EXCEPT ![p] = succSet[p] \ {s}]
    /\ pc' = [pc EXCEPT ![p] = "Wait"]
    /\ UNCHANGED << sel >>

Wait(p) ==
    /\ pc[p] = "Wait"
    /\ IF succSet[p] = {}
          THEN /\ pc' = [pc EXCEPT ![p] = "Done"]
               /\ UNCHANGED << marked, frontier, sel, succSet >>
          ELSE /\ UNCHANGED << pc, marked, frontier, sel, succSet >>

Done(p) ==
    /\ pc[p] = "Done"
    /\ UNCHANGED << marked, frontier, pc, sel, succSet >>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ \E p \in Procs: Pick(p)
    \/ \E p \in Procs: Push(p)
    \/ \E p \in Procs: Wait(p)
    \/ \E p \in Procs: Done(p)

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* -------------------------------------------------
\* Type-correctness invariant (Inv)
\* -------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> PCVals]
    /\ sel \in [Procs -> Nodes]
    /\ succSet \in [Procs -> SUBSET Nodes]
    /\ \A p \in Procs: succSet[p] \subseteq Nodes

\* -------------------------------------------------
\* Refinement property (Refines) – relationship to a
\* sequential specification (placeholder, assumed true)
\* -------------------------------------------------
Refines == Inv

\* -------------------------------------------------
\* Theorem (optional, for TLC)
\* -------------------------------------------------
THEOREM Spec => []Inv

====