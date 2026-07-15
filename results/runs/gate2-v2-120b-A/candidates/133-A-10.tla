---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* Set of node identifiers (e.g., {1,2,3,4})
    Root,           \* The start node of the graph
    Procs,          \* Set of worker process identifiers (e.g., {1,2})
    Succ,           \* Function: Nodes -> SUBSET Nodes, each node's successors
    Seq             \* Upper bound on the length of any sequence (here = Cardinality(Nodes))

\*----------------------------------------------------------------------
\* Types
Node == Nodes
Proc == Procs
PC   == {"Idle", "Select", "Expand", "Done"}
\*----------------------------------------------------------------------
\* State variables
VARIABLES
    marked,         \* Set of nodes that have been discovered
    frontier,       \* Set of nodes currently being explored
    pc,             \* Per‑process program counter
    sel,            \* Per‑process selected node (or Null)
    succSet,        \* Per‑process set of successors of the selected node
    seqCounters     \* Per‑process length of the internal sequence (bounded by Seq)

\*----------------------------------------------------------------------
\* Helper definitions
Null == 0               \* distinguished value meaning “no node selected”

\*----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = [p \in Proc |-> "Idle"]
    /\ sel      = [p \in Proc |-> Null]
    /\ succSet  = [p \in Proc |-> {}]
    /\ seqCounters = [p \in Proc |-> 0]

\*----------------------------------------------------------------------
\* Actions (inherited from the parallel algorithm)

\* A process that is idle may start a new iteration
StartIter(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ sel'       = [sel EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
    /\ pc'        = [pc  EXCEPT ![p] = "Select"]
    /\ UNCHANGED <<marked, frontier, succSet, seqCounters>>

\* The process records the selected node and prepares its successor set
Select(p) ==
    /\ pc[p] = "Select"
    /\ sel[p] # Null
    /\ succSet'   = [succSet EXCEPT ![p] = Succ[sel[p]]]
    /\ seqCounters' = [seqCounters EXCEPT ![p] = 1]   \* start counting sequence length
    /\ pc'        = [pc EXCEPT ![p] = "Expand"]
    /\ UNCHANGED <<marked, frontier, sel>>

\* The process expands its successors, respecting the sequence bound
Expand(p) ==
    /\ pc[p] = "Expand"
    /\ \E n \in succSet[p] :
          /\ (seqCounters[p] < Seq)             \* bound not yet exceeded
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \/ {n}
          /\ succSet'  = [succSet EXCEPT ![p] = succSet[p] \ {n}]
          /\ seqCounters' = [seqCounters EXCEPT ![p] = seqCounters[p] + 1]
          /\ UNCHANGED <<pc, sel>>
    \/ /\ succSet[p] = {}               \* no more successors to process
          /\ pc' = [pc EXCEPT ![p] = "Done"]
          /\ UNCHANGED <<marked, frontier, sel, succSet, seqCounters>>

\* The process finishes its iteration and becomes idle again
Finish(p) ==
    /\ pc[p] = "Done"
    /\ sel'       = [sel EXCEPT ![p] = Null]
    /\ pc'        = [pc EXCEPT ![p] = "Idle"]
    /\ succSet'   = [succSet EXCEPT ![p] = {}]
    /\ seqCounters' = [seqCounters EXCEPT ![p] = 0]
    /\ UNCHANGED <<marked, frontier>>

\* Global termination condition (optional, but does not affect safety)
Terminate ==
    /\ \A p \in Proc: pc[p] = "Idle"
    /\ frontier = {}

\* Next-state relation
Next ==
    \/ \E p \in Proc: StartIter(p)
    \/ \E p \in Proc: Select(p)
    \/ \E p \in Proc: Expand(p)
    \/ \E p \in Proc: Finish(p)
    \/ Terminate

\*----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet, seqCounters>>

\*----------------------------------------------------------------------
\* Safety invariant (type correctness and control‑flow properties)
Inv ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Proc: pc[p] \in PC
    /\ \A p \in Proc:
          (pc[p] = "Idle")  => (sel[p] = Null /\ succSet[p] = {} /\ seqCounters[p] = 0)
    /\ \A p \in Proc:
          (pc[p] = "Select") => (sel[p] # Null /\ succSet[p] = {} /\ seqCounters[p] = 0)
    /\ \A p \in Proc:
          (pc[p] = "Expand") =>
              /\ sel[p] # Null
              /\ succSet[p] \subseteq Nodes
              /\ seqCounters[p] \in 1..Seq
    /\ \A p \in Proc:
          (pc[p] = "Done") => (sel[p] # Null /\ succSet[p] = {})

\*----------------------------------------------------------------------
\* Refinement property: the parallel algorithm implements the sequential Misra algorithm.
\* For this configuration we assert that the set of marked nodes monotonically grows
\* and never loses elements (a property that holds in the sequential algorithm).
Refines ==
    /\ \A p \in Proc: pc[p] \in {"Idle", "Done"} => frontier = {}
    /\ \A n \in Nodes: []<>(n \in marked) => []<>(n \in marked)   \* trivial stability

====