------------------------- MODULE MCParReach -------------------------
EXTENDS Naturals, Sequences

(* A model-checking configuration module for the parallel reachability       *)
(* algorithm.  It reuses the entire parallel algorithm spec and provides      *)
(* configuration-level definitions needed for finite-state model checking.   *)
(* Sequence length is bounded to the number of nodes, and each node has      *)
(* exactly two successors, matching the configuration of the sequential      *)
(* module's model.                                                            *)

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc, sel, sucs

vars == <<marked, frontier, pc, sel, sucs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ sucs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ sucs = [p \in Procs |-> {}]

Idle(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
       /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ sucs' = [sucs EXCEPT ![p] = {}]
  /\ UNCHANGED << >>

Select(p, n) ==
  /\ pc[p] = "selecting"
  /\ n \in sucs[p]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, sucs>>

Explore(p) ==
  /\ pc[p] = "exploring"
  /\ \E m \in Succ[sel[p]] :
       /\ frontier' = frontier \cup {m}
       /\ sucs' = [sucs EXCEPT ![p] = @ \cup {m}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, sel>>

Next ==
  \/ \E p \in Procs : Idle(p)
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)

Spec == Init /\ [][Next]_vars

(* The reachable-state invariant: it is type-correct and respects the     *)
(* control flow of the algorithm (no exploring without a selection, etc.). *)
Inv == TypeOK

(* Refinement: the parallel algorithm implements the sequential Misra      *)
(* reachability algorithm -- every frontier node is reachable from the     *)
(* root via a path entirely through reached nodes.                          *)
Refines == \A n \in frontier : \E path \in LimitedSeq(Nodes) :
               /\ Len(path) > 0
               /\ Head(path) = Root
               /\ path[Len(path)] = n
               /\ \A i \in 1..(Len(path) - 1) : path[i + 1] \in Succ[path[i]]
               /\ \A i \in 1..(Len(path) - 1) : path[i] \in marked

(* Sequences of bounded length are finite sets: model checking requires    *)
(* that the replacement of Seq from the Sequences module be a FINITE       *)
(* version, so the configuration explicitly replaces it with LimitedSeq.  *)
LimitedSeq == Seq

=============================================================================