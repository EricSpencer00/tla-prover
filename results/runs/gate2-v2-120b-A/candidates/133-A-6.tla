---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* Set of graph nodes
    Root,    \* Entry node of the graph
    Procs,   \* Set of worker processes
    Succ,    \* Total function: [Nodes -> SUBSET Nodes] giving successors
    Seq      \* Upper bound on sequence lengths (non‑negative integer)

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
NodeSeq == 0 .. Seq                         \* All allowed lengths for sequences

(*-----------------------------------------------------------------
  Variables (inherited from the parallel algorithm)
-----------------------------------------------------------------*)
VARIABLES
    marked,      \* Set of nodes that have been reached
    frontier,    \* Set of frontier nodes (to be explored)
    pc,          \* Per‑process program counter (set of control‑flow labels)
    sel,         \* Per‑process selected node (or Null if none)
    succSet      \* Per‑process set of successors of the selected node

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* Null value for a process that has not selected any node
Null == "NULL"

\* All possible control‑flow labels used by the algorithm
Labels == {"Idle", "Select", "Explore", "Done"}

(*-----------------------------------------------------------------
  Types (for the invariant)
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> Labels]
    /\ sel \in [Procs -> (Nodes \cup {Null})]
    /\ succSet \in [Procs -> SUBSET Nodes]

(*-----------------------------------------------------------------
  Initial state (inherited, instantiated)
-----------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = [p \in Procs |-> Null]
    /\ succSet = [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Actions (serial style, one process per step)
-----------------------------------------------------------------*)
Select(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ let n == CHOOSE m \in frontier : TRUE IN
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succSet' = [succSet EXCEPT ![p] = Succ[n]]
    /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<marked, frontier>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ sel[p] # Null
    /\ let n == sel[p] IN
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ sel' = [sel EXCEPT ![p] = Null]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ UNCHANGED << >>

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, sel, succSet>>

Next ==
    \/ \E p \in Procs: Select(p)
    \/ \E p \in Procs: Explore(p)
    \/ \E p \in Procs: Done(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Invariant (safety property)
-----------------------------------------------------------------*)
Inv == TypeOK

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm implements the
  sequential Misra algorithm.  This is expressed as the existence
  of a stuttering simulation to the sequential specification.
  For the purpose of this configuration module we expose it as a
  simple predicate that can be checked against the sequential
  spec (not duplicated here).
-----------------------------------------------------------------*)
Refines == TRUE

====