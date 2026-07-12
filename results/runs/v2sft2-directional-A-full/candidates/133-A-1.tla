---- MODULE MCParReach ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

(* Type correctness constants *)
Nodes \* a finite set of nodes
Root \* a distinguished node in Nodes
Procs \* a finite set of process identifiers
Succ \* a total function from Nodes to a non-empty finite set of Nodes
Seq \* a function mapping each node to a bounded sequence of nodes

(* Derived constants *)
NODES == Nodes
ROOT == Root
PROCSET == Procs
SUCC == Succ
SEQ == Seq

VARIABLES marked, frontier, pc, selected, succSet

(* ----------------------------------------------------------------------
   State decomposition
   ---------------------------------------------------------------------- *)
(* marked : a subset of Nodes that have been discovered *)
(* frontier: a set of nodes currently awaiting exploration *)
(* pc : per-process program counter, each taking values in {"Init", "Select", "Check", "Update"} *)
(* selected : per-process selected node, a node or NULL *)
(* succSet : per-process set of successor nodes for the selected node *)

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {ROOT}
    /\ frontier = {ROOT}
    /\ pc = [p \in PROCSET |-> "Init"]
    /\ selected = [p \in PROCSET |-> NULL]
    /\ succSet = [p \in PROCSET |-> {}]

(* ----------------------------------------------------------------------
   Actions (identical to the parallel reachability algorithm)
   ---------------------------------------------------------------------- *)
Select(p) ==
    /\ pc[p] = "Init"
    /\ UNCHANGED << marked, frontier, succSet >>
    /\ selected' = [selected EXCEPT ![p] = CHOOSE n \in frontier : n]
    /\ pc' = [pc EXCEPT ![p] = "Select"]

Check(p) ==
    /\ pc[p] = "Select"
    /\ selected[p] # NULL
    /\ UNCHANGED << marked, frontier, succSet >>
    /\ pc' = [pc EXCEPT ![p] = "Check"]

Update(p) ==
    /\ pc[p] = "Check"
    /\ selected[p] # NULL
    /\ succSet' = [succSet EXCEPT ![p] = SUCC[selected[p]]]
    /\ frontier' = frontier \ {selected[p]} \ (marked \ succSet'[p])
    /\ marked' = marked \cup succSet'[p]
    /\ pc' = [pc EXCEPT ![p] = "Update"]
    /\ selected' = [selected EXCEPT ![p] = NULL]

(* The NEXT relation permits any enabled process to take its next step *)
Next ==
    \E p \in PROCSET :
        \E action \in {Select, Check, Update} :
            action(p)

Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

(* ----------------------------------------------------------------------
   Safety invariant: type correctness and control-flow discipline
   ---------------------------------------------------------------------- *)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in PROCSET :
          pc[p] \in {"Init", "Select", "Check", "Update"}
    /\ \A p \in PROCSET :
          selected[p] \in Nodes \cup {NULL}
    /\ \A p \in PROCSET :
          succSet[p] \subseteq Nodes

(* ----------------------------------------------------------------------
   Refinement property: the parallel algorithm implements the sequential Misra algorithm
   (this is a placeholder representing the intended refinement relation)
   ---------------------------------------------------------------------- *)
Refines ==
    (* The sequential algorithm's state would be represented by a separate module; here we assert that
       the set of marked nodes in the parallel algorithm matches the set of nodes that would be marked
       by the sequential algorithm after exploring the same nodes. *)
    marked = \E visited \in SUBSET Nodes :
              visited = SET {
                  n \in visited :
                      n = ROOT \/ (EXISTS p \in PROCSET :
                          n \in SUCC[\* selected[p] \in visited])
              }

====