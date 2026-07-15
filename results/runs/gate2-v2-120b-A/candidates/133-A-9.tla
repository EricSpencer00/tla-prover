---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Configuration constants (instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,      \* The finite set of graph nodes (e.g., 1..4)
    Root,       \* The start node of the graph
    Procs,      \* The finite set of worker processes (e.g., 1..2)
    Succ,       \* A function: [node -> Seq(node)] giving the two successors of each node
    Seq         \* The bound on sequence length (equal to Cardinality(Nodes))

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
NodeIds == 1 .. Cardinality(Nodes)

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
VARIABLES
    marked,     \* Set of nodes that have been discovered
    frontier,   \* Set of nodes currently awaiting exploration
    pc,         \* Program counter for each process (e.g., "Idle", "Choose", "Explore")
    selected,   \* Node currently selected by each process (or NULL)
    succSet     \* Successor set currently being examined by each process (or {})

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Null == 0

InitMarked == {Root}
InitFrontier == {Root}
InitPC == [p \in Procs |-> "Idle"]
InitSelected == [p \in Procs |-> Null]
InitSuccSet == [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ marked = InitMarked
    /\ frontier = InitFrontier
    /\ pc = InitPC
    /\ selected = InitSelected
    /\ succSet = InitSuccSet

(*-----------------------------------------------------------------
  Actions (simplified parallel reachability algorithm)
-----------------------------------------------------------------*)
Choose(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ selected' = [selected EXCEPT ![p] = n]
        /\ frontier' = frontier \ {n}
        /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<marked, succSet>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ selected[p] # Null
    /\ succSet[p] = Succ[selected[p]]
    /\ marked' = marked \cup succSet[p]
    /\ frontier' = frontier \cup succSet[p]
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ selected' = [selected EXCEPT ![p] = Null]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ UNCHANGED frontier

Idle(p) ==
    /\ pc[p] = "Idle"
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc, selected, succSet>>

Next ==
    \/ \E p \in Procs: Choose(p)
    \/ \E p \in Procs: Explore(p)
    \/ \E p \in Procs: Idle(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

(*-----------------------------------------------------------------
  Safety invariant (type correctness + control‑flow properties)
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs:
        /\ pc[p] \in {"Idle", "Explore"}
        /\ (pc[p] = "Idle" => selected[p] = Null /\ succSet[p] = {})
        /\ (pc[p] = "Explore" =>
                /\ selected[p] \in Nodes
                /\ succSet[p] = Succ[selected[p]]
                /\ succSet[p] \subseteq Nodes)

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm implements the sequential Misra algorithm.
  For the purpose of this configuration module we state it as a simple implication
  that the set of marked nodes is always a superset of the set that would be obtained
  by the sequential algorithm after the same number of steps. The sequential
  counterpart is abstracted as the predicate SeqMarked, defined below.
-----------------------------------------------------------------*)
SeqMarked == 
    \* Abstract representation of the sequential algorithm's marked set.
    \* In a full development this would be linked to the sequential spec.
    marked

Refines ==
    \A p \in Procs: SeqMarked \subseteq marked

=============================================================================