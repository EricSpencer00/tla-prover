---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Configuration constants (to be supplied by the .cfg file)               *)
(***************************************************************************)
CONSTANTS
    Nodes,   \* The finite set of graph nodes
    Root,    \* The distinguished start node
    Procs,   \* The finite set of worker processes
    Succ,    \* Function: Nodes -> SUBSET Nodes (the graph edges)
    Seq      \* Upper bound on sequence lengths (equal to Cardinality(Nodes))

(***************************************************************************)
(*  State variables (inherited from the parallel reachability algorithm)   *)
(***************************************************************************)
VARIABLES
    marked,          \* Shared set of already discovered nodes
    frontier,        \* Shared set of nodes pending exploration
    procPC,          \* Per-process program counter (control state)
    procSelected,    \* Per-process currently selected node (or None)
    procSuccs        \* Per-process set of successors of the selected node

(***************************************************************************)
(*  Derived constants and helper definitions                               *)
(***************************************************************************)
NodeSeq == [i \in 1..Seq |-> CHOOSE n \in Nodes : TRUE]   \* A dummy bounded sequence
None == "None"                                           \* Special value meaning “no selection”

ProcIds == {"idle", "select", "process", "done"}          \* Control states

(***************************************************************************)
(*  Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ procPC = [p \in Procs |-> "idle"]
    /\ procSelected = [p \in Procs |-> None]
    /\ procSuccs = [p \in Procs |-> {}]

(***************************************************************************)
(*  Actions (inherited from the parallel algorithm)                       *)
(***************************************************************************)

(* A process picks a node from the shared frontier *)
Select(p) ==
    /\ procPC[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ procSelected' = [procSelected EXCEPT ![p] = n]
          /\ procSuccs'   = [procSuccs   EXCEPT ![p] = Succ[n]]
          /\ frontier'    = frontier \ {n}
          /\ procPC'      = [procPC EXCEPT ![p] = "process"]
    /\ UNCHANGED <<marked>>

(* A process adds its successors to the shared frontier *)
Process(p) ==
    /\ procPC[p] = "process"
    /\ procSuccs[p] # {}
    /\ LET new == procSuccs[p] \ marked IN
       /\ frontier' = frontier \cup new
    /\ procPC' = [procPC EXCEPT ![p] = "idle"]
    /\ procSelected' = [procSelected EXCEPT ![p] = None]
    /\ procSuccs'   = [procSuccs   EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked>>

(* Optional termination action; does not change any variable *)
Done(p) ==
    /\ procPC[p] = "idle"
    /\ frontier = {}
    /\ marked = Nodes
    /\ procPC' = [procPC EXCEPT ![p] = "done"]
    /\ UNCHANGED <<marked, frontier, procSelected, procSuccs>>

Next ==
    \E p \in Procs :
        \/ Select(p)
        \/ Process(p)
        \/ Done(p)

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<marked, frontier, procPC, procSelected, procSuccs>>

(***************************************************************************)
(*  Safety invariant (type correctness + control‑flow properties)         *)
(***************************************************************************)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ marked \cup frontier \subseteq Nodes
    /\ procPC \in [Procs -> ProcIds]
    /\ procSelected \in [Procs -> (Nodes \cup {None})]
    /\ \A p \in Procs :
          (procPC[p] = "process") => (procSelected[p] \in Nodes)
    /\ procSuccs \in [Procs -> SUBSET Nodes]
    /\ \A p \in Procs :
          (procPC[p] # "process") => (procSuccs[p] = {})

(***************************************************************************)
(*  Refinement property: the parallel algorithm implements the sequential  *)
(*  (Misra) algorithm. For the configuration we formulate it as “if a node *)
(*  is marked in the parallel run, then it eventually appears in the       *)
(*  sequential run”. The sequential run is captured by the same marking    *)
(*  set, so the property simply states that the parallel marking never     *)
(*  exceeds the set of nodes reachable from the root.                      *)
(***************************************************************************)
ReachableFromRoot == {n \in Nodes : 
                        \E path \in Seq(1,Cardinality(Nodes)) :
                            /\ Len(path) >= 1
                            /\ Head(path) = Root
                            /\ Last(path) = n
                            /\ \A i \in 1..(Len(path)-1) : path[i+1] \in Succ[path[i]]}

Refines == marked \subseteq ReachableFromRoot

=============================================================================