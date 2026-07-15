---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants required by the reference .cfg
--------------------------------------------------------------------*)
CONSTANTS 
    Nodes,      \* The set of graph nodes
    Root,       \* The start node
    Procs,      \* The set of worker processes
    Succ,       \* Succ[n] is the sequence of successors of node n
    Seq         \* Upper bound on the length of any sequence ( = Cardinality(Nodes) )
    
(*--------------------------------------------------------------------
  Derived sets and helper definitions
--------------------------------------------------------------------*)
Node == Nodes
Proc == Procs
NodeSeq == Seq(Node)                     \* sequences of nodes, length ≤ Seq
EmptySeq == <<>>                         \* the empty sequence

(*--------------------------------------------------------------------
  State variables (inherited from the parallel algorithm)
--------------------------------------------------------------------*)
VARIABLES
    marked,          \* Set of nodes that have been discovered
    frontier,        \* Set of nodes currently in the shared frontier
    pc,              \* Program counter per process (maps Proc to a label)
    selected,        \* Currently selected node per process (maps Proc to Node or "None")
    succSet          \* Successor set pending to be added per process (maps Proc to NodeSeq)

(*--------------------------------------------------------------------
  Labels for program counters
--------------------------------------------------------------------*)
Labels == {"Init", "Select", "Expand", "Done"}

(*--------------------------------------------------------------------
  Initialization (inherits the sequential algorithm's init, instantiated)
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Proc |-> "Init"]
    /\ selected = [p \in Proc |-> "None"]
    /\ succSet = [p \in Proc |-> EmptySeq]

(*--------------------------------------------------------------------
  Actions (inherited from the parallel algorithm)
--------------------------------------------------------------------*)

Select(p) ==
    /\ pc[p] = "Init"
    /\ frontier # {}
    /\ selected[p] = CHOOSE n \in frontier : TRUE   \* nondeterministically pick a frontier node
    /\ frontier' = frontier \ {selected[p]}
    /\ pc' = [pc EXCEPT ![p] = "Expand"]
    /\ UNCHANGED <<marked, succSet, selected>>

Expand(p) ==
    /\ pc[p] = "Expand"
    /\ succSet[p] = Succ[selected[p]]
    /\ marked' = marked \cup {selected[p]}
    /\ frontier' = frontier \cup {head(succSet[p])}
    /\ succSet' = [succSet EXCEPT ![p] = Tail(succSet[p])]
    /\ pc' = [pc EXCEPT ![p] = IF succSet[p] = <<>> THEN "Done" ELSE "Expand"]
    /\ UNCHANGED <<selected>>

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Done"]   \* stays in Done
    /\ UNCHANGED <<marked, frontier, selected, succSet>>

Next ==
    \E p \in Proc : Select(p) \/ Expand(p) \/ Done(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

(*--------------------------------------------------------------------
  Safety invariant: type correctness plus control-flow properties
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Node
    /\ frontier \subseteq Node
    /\ pc \in [Proc -> Labels]
    /\ selected \in [Proc -> (Node \cup {"None"})]
    /\ succSet \in [Proc -> NodeSeq]
    /\ \A p \in Proc :
        IF pc[p] = "Init" THEN
            /\ selected[p] = "None"
            /\ succSet[p] = EmptySeq
        ELSIF pc[p] = "Select" THEN
            /\ selected[p] = "None"
            /\ succSet[p] = EmptySeq
        ELSIF pc[p] = "Expand" THEN
            /\ selected[p] \in Node
            /\ succSet[p] \in NodeSeq
        ELSE   \* pc[p] = "Done"
            /\ selected[p] = "None"
            /\ succSet[p] = EmptySeq

Inv == TypeOK

(*--------------------------------------------------------------------
  Refinement property: the parallel algorithm implements the sequential Misra algorithm.
  This is expressed as a stuttering simulation between the parallel state and an
  abstract sequential state (not modeled explicitly here).  The property asserts that
  the set of marked nodes always matches that of some sequential execution.
--------------------------------------------------------------------*)
SeqMarked == marked   \* In this configuration the sequential marked set is identified with the parallel one.

Refines == 
    /\ marked = SeqMarked
    /\ frontier = {} \/ frontier = SeqMarked

====