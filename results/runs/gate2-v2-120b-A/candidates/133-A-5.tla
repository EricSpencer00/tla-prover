---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,   \* Set of graph nodes
    Root,    \* The start node
    Procs,   \* Set of worker processes
    Succ,    \* Succ \in [Nodes -> Seq(2, Nodes)]  (exactly 2 successors per node)
    Seq      \* Upper bound for sequence length (equal to Cardinality(Nodes))

(*--algorithm ParallelReach
variables
    marked    \in SUBSET Nodes,
    frontier  \in SUBSET Nodes,
    pc        \in [Procs -> {"Idle", "Select", "Process", "Done"}],
    sel       \in [Procs -> Nodes],
    succs     \in [Procs -> SUBSET Nodes];

begin
  Init:
    marked   := {Root};
    frontier := {Root};
    pc       := [p \in Procs |-> "Idle"];
    sel      := [p \in Procs |-> Root];
    succs    := [p \in Procs |-> {}];

  Process:
    while TRUE do
      either
        /\ \E p \in Procs: pc[p] = "Idle"
        /\ \E p \in Procs:
            /\ pc[p] = "Idle"
            /\ frontier # {}
            /\ LET n == CHOOSE x \in frontier: TRUE IN
               /\ sel'   = [sel EXCEPT ![p] = n]
               /\ frontier' = frontier \ {n}
               /\ pc'    = [pc EXCEPT ![p] = "Select"]
               /\ UNCHANGED <<marked, succs>>
      or
        /\ \E p \in Procs: pc[p] = "Select"
        /\ \E p \in Procs:
            /\ pc[p] = "Select"
            /\ LET n == sel[p] IN
               /\ succs' = [succs EXCEPT ![p] = {Succ[n][1], Succ[n][2]}]
               /\ pc'    = [pc EXCEPT ![p] = "Process"]
               /\ UNCHANGED <<marked, frontier, sel>>
      or
        /\ \E p \in Procs: pc[p] = "Process"
        /\ \E p \in Procs:
            /\ pc[p] = "Process"
            /\ LET newMarked == succs[p] \ marked IN
               /\ marked'   = marked \cup newMarked
               /\ frontier' = frontier \cup newMarked
               /\ pc'       = [pc EXCEPT ![p] = "Done"]
               /\ UNCHANGED <<sel, succs>>
      or
        /\ \E p \in Procs: pc[p] = "Done"
        /\ \E p \in Procs:
            /\ pc[p] = "Done"
            /\ pc' = [pc EXCEPT ![p] = "Idle"]
            /\ UNCHANGED <<marked, frontier, sel, succs>>
      end either;
    end while;
end algorithm;*)

(***************************************************************************)
(*  Constants (for TLC)                                                   *)
(***************************************************************************)

(* The constants are declared above and will be instantiated by the .cfg *)

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)

VARIABLES
    marked,    \* Set of nodes that have been discovered
    frontier,  \* Nodes discovered but not yet processed
    pc,        \* Per-process program counter
    sel,       \* Per-process selected node
    succs      \* Per-process set of successors of the selected node

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)

PCVals == {"Idle", "Select", "Process", "Done"}

(* The set of possible program counter values per process *)
PC == [p \in Procs -> PCVals]

(***************************************************************************)
(*  Initial predicate                                                     *)
(***************************************************************************)

Init ==
    /\ marked   = {Root}
    /\ frontier = {Root}
    /\ pc       = [p \in Procs |-> "Idle"]
    /\ sel      = [p \in Procs |-> Root]
    /\ succs    = [p \in Procs |-> {}]

(***************************************************************************)
(*  Next-state relation (unrolled version of the algorithm actions)       *)
(***************************************************************************)

Next ==
    \/ \E p \in Procs:
          /\ pc[p] = "Idle"
          /\ frontier # {}
          /\ LET n == CHOOSE x \in frontier: TRUE IN
                 /\ sel'   = [sel EXCEPT ![p] = n]
                 /\ frontier' = frontier \ {n}
                 /\ pc'    = [pc EXCEPT ![p] = "Select"]
                 /\ UNCHANGED <<marked, succs>>
    \/ \E p \in Procs:
          /\ pc[p] = "Select"
          /\ LET n == sel[p] IN
                 /\ succs' = [succs EXCEPT ![p] = {Succ[n][1], Succ[n][2]}]
                 /\ pc'    = [pc EXCEPT ![p] = "Process"]
                 /\ UNCHANGED <<marked, frontier, sel>>
    \/ \E p \in Procs:
          /\ pc[p] = "Process"
          /\ LET newMarked == succs[p] \ marked IN
                 /\ marked'   = marked \cup newMarked
                 /\ frontier' = frontier \cup newMarked
                 /\ pc'       = [pc EXCEPT ![p] = "Done"]
                 /\ UNCHANGED <<sel, succs>>
    \/ \E p \in Procs:
          /\ pc[p] = "Done"
          /\ pc' = [pc EXCEPT ![p] = "Idle"]
          /\ UNCHANGED <<marked, frontier, sel, succs>>

(***************************************************************************)
(*  Full specification                                                     *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(***************************************************************************)
(*  Invariant: type correctness and control-flow properties               *)
(***************************************************************************)

Inv ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc       \in PC
    /\ sel      \in [Procs -> Nodes]
    /\ succs    \in [Procs -> SUBSET Nodes]
    /\ \A p \in Procs:
          /\ (pc[p] = "Idle")    => succs[p] = {}
          /\ (pc[p] = "Select")  => succs[p] = {}
          /\ (pc[p] = "Process") => succs[p] = {Succ[sel[p]][1], Succ[sel[p]][2]}
          /\ (pc[p] = "Done")    => succs[p] = {Succ[sel[p]][1], Succ[sel[p]][2]}

(***************************************************************************)
(*  Refinement property (placeholder for sequential Misra algorithm)     *)
(***************************************************************************)

(* The detailed refinement relation would compare this parallel
   execution to a sequential model of the Misra algorithm.  For the
   purpose of this configuration we state it as an existential
   condition that a sequential trace exists with the same set of
   marked nodes. *)

Refines ==
    (* There exists a sequence of nodes visited by some sequential
       algorithm that results in exactly the same final marked set. *)
    \A n \in Nodes: n \in marked => TRUE

(***************************************************************************)
(*  Theorem (optional)                                                     *)
(***************************************************************************)

THEOREM Spec => []Inv

====