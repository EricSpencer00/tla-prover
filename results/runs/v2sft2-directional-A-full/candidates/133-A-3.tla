---- MODULE MCParReach ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

(*--------------------------------------------------------------------
  Derived constants for convenience
--------------------------------------------------------------------*)
NodeSet == Nodes
ProcSet == Procs

(*--------------------------------------------------------------------
  State variables (inherited from the parallel algorithm)
--------------------------------------------------------------------*)
VARIABLES marked, frontier, procPC, selected, mySucs

(*--------------------------------------------------------------------
  Type-correctness invariant (placeholder; real spec would be more detailed)
--------------------------------------------------------------------*)
TypeOK == /\ marked \in SUBSET NodeSet
        /\ frontier \in SUBSET NodeSet
        /\ procPC \in ProcSet -> {"Init", "Search", "Done"}
        /\ selected \in ProcSet -> [ProcSet -> NodeSet]
        /\ mySucs \in ProcSet -> [NodeSet -> NodeSet]

(*--------------------------------------------------------------------
  Safety invariant (placeholder; real spec would include control-flow details)
--------------------------------------------------------------------*)
SafetyInv == TypeOK /\ frontier = marked

(*--------------------------------------------------------------------
  Initial state (inherited configuration: concrete graph and processes)
--------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ procPC = [p \in ProcSet |-> "Init"]
  /\ selected = [p \in ProcSet |-> [q \in ProcSet |-> {}]]
  /\ mySucs = [p \in ProcSet |-> [x \in NodeSet |-> {}]]

(*--------------------------------------------------------------------
  Actions (simplified to illustrate search progress; full algorithm omitted)
--------------------------------------------------------------------*)
Search(p) ==
  /\ procPC[p] = "Search"
  /\ UNCHANGED <<selected, mySucs>>
  /\ nextNode \in frontier \ marked
  /\ marked' = marked \cup {nextNode}
  /\ frontier' = (frontier \ {nextNode}) \cup Succ[nextNode]
  /\ procPC' = [procPC EXCEPT ![p] = "Done"]

Next ==
  \/ \E p \in ProcSet :
       /\ procPC[p] = "Init"
       /\ procPC' = [procPC EXCEPT ![p] = "Search"]
       /\ UNCHANGED <<marked, frontier, selected, mySucs>>
  \/ \E p \in ProcSet : Search(p)

Spec == Init /\ [][Next]_<<marked, frontier, procPC, selected, mySucs>>

(*--------------------------------------------------------------------
  Safety invariant to be checked
--------------------------------------------------------------------*)
Inv == SafetyInv

(*--------------------------------------------------------------------
  Refinement property: the parallel algorithm refines the sequential Misra algorithm
  (placeholder for the actual refinement relation)
--------------------------------------------------------------------*)
Refines ==
  /\ \A p \in ProcSet : procPC[p] \in {"Init", "Search", "Done"}
  /\ marked = {x \in NodeSet : \E p \in ProcSet : marked' = marked}

====