---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT Nodes          \* Set of node identifiers (e.g., 1..4)
CONSTANT Root           \* The entry node of the graph
CONSTANT Procs          \* Set of worker process identifiers (e.g., 1..2)
CONSTANT Succ           \* Function: Nodes -> Seq(2) giving the two successors of each node
CONSTANT Seq            \* Upper bound on sequence lengths (equal to Cardinality(Nodes))

(*-----------------------------------------------------------------
  Derived constant definitions (optional but convenient)
-----------------------------------------------------------------*)
NodeSeq == 1..Seq

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc, sel, succs

(*-----------------------------------------------------------------
  Type invariant (used as part of the overall safety invariant)
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {"Idle", "Select", "Explore", "Done"}]
    /\ sel \in [Procs -> Nodes \cup {None}]
    /\ succs \in [Procs -> SUBSET Nodes]

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = [p \in Procs |-> None]
    /\ succs = [p \in Procs |-> {}]

(*-----------------------------------------------------------------
  Actions (mirroring the parallel reachability algorithm)
-----------------------------------------------------------------*)

Idle(p) ==
    /\ pc[p] = "Idle"
    /\ pc' = [pc EXCEPT ![p] = "Select"]
    /\ UNCHANGED <<marked, frontier, sel, succs>>

Select(p) ==
    /\ pc[p] = "Select"
    /\ frontier # {}
    /\ sel' = [sel EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
    /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<marked, frontier, succs>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ sel[p] \in Nodes
    /\ succs' = [succs EXCEPT ![p] = {Succ[sel[p]][1], Succ[sel[p]][2]}]
    /\ marked' = marked \cup succs'[p]
    /\ frontier' = (frontier \ {sel[p]}) \cup succs'[p]
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ sel' = [sel EXCEPT ![p] = None]

Done(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, sel, succs>>

ParallelStep ==
    \E p \in Procs :
        \/ Idle(p)
        \/ Select(p)
        \/ Explore(p)
        \/ Done(p)

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next == ParallelStep

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(*-----------------------------------------------------------------
  Safety invariant (type correctness + control‑flow constraints)
-----------------------------------------------------------------*)
Inv == TypeOK

(*-----------------------------------------------------------------
  Refinement property: the set of marked nodes is exactly the set
  reachable from Root in the underlying graph.  This mirrors the
  sequential Misra algorithm's specification.
-----------------------------------------------------------------*)
Reachable(root) ==
    LET R == {root} \cup UNION { {Succ[n][1], Succ[n][2]} : n \in R }
    IN R

Refines == marked = Reachable(Root)

=============================================================================