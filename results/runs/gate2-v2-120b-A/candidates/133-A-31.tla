---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  Configuration constants (must be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* Set of node identifiers
    Root,    \* The initial node of the graph
    Procs,   \* Set of worker process identifiers
    Succ,    \* Total successor relation: a function from each node to a set of exactly two successors
    Seq      \* Upper bound on the length of any sequence (equal to Cardinality(Nodes))

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
NodeSeq == 1..Seq

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    marked,      \* Set of nodes that have been discovered
    frontier,    \* Set of nodes currently being explored
    pc,          \* Program counter per process (e.g., "Init", "Select", "Explore", "Done")
    selected,   \* Node currently selected by each process (or 0 if none)
    succs        \* Successor set known to each process for its selected node

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
ProcSet == Procs

(* Initial state *)
Init ==
    /\ marked   = {}
    /\ frontier = {}
    /\ pc       = [p \in ProcSet |-> "Init"]
    /\ selected = [p \in ProcSet |-> 0]
    /\ succs    = [p \in ProcSet |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
InitAction ==
    Init

Select(p) ==
    /\ pc[p] = "Init"
    /\ selected' = [selected EXCEPT ![p] = Root]
    /\ succs'    = [succs EXCEPT ![p] = Succ[Root]]
    /\ pc'       = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<marked, frontier>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ frontier' = frontier \cup {selected[p]}
    /\ marked'   = marked \cup {selected[p]}
    /\ pc'       = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<selected, succs>>

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<marked, frontier, selected, succs>>

(* Parallel composition of all actions *)
Next ==
    \E p \in ProcSet :
        \/ Select(p)
        \/ Explore(p)
        \/ Done(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succs>>

(*-----------------------------------------------------------------
  Safety invariant (type correctness + control flow)
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc       \in [ProcSet -> {"Init", "Explore", "Done"}]
    /\ selected \in [ProcSet -> (Nodes \cup {0})]
    /\ succs    \in [ProcSet -> SUBSET Nodes]

ControlFlow ==
    \A p \in ProcSet :
        /\ pc[p] = "Init"    => selected[p] = 0
        /\ pc[p] = "Explore" => selected[p] \in Nodes /\ succs[p] = Succ[selected[p]]
        /\ pc[p] = "Done"    => selected[p] \in Nodes

Inv == TypeOK /\ ControlFlow

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm should implement the
  sequential Misra algorithm (abstracted as the existence of a
  bijection between the parallel marked set and the sequential
  marked set).  Here we capture it as an existence of a sequence
  of explored nodes that respects the sequential graph traversal.
-----------------------------------------------------------------*)
Refines ==
    \E seq \in SeqSeq :
        /\ Len(seq) <= Seq
        /\ seq[1] = Root
        /\ \A i \in 1..Len(seq)-1 :
               seq[i+1] \in Succ[seq[i]]
        /\ marked = {seq[i] : i \in 1..Len(seq)}

(*-----------------------------------------------------------------
  Helper: the set of all finite sequences over Nodes with length ≤ Seq
-----------------------------------------------------------------*)
SeqSeq == { s \in Seq(1..Seq, Nodes) : Len(s) <= Seq }

====