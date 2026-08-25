---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

(*----------------------------------------------------*)
(* Initial state *)
Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> << >>]               \* each process starts with an empty sequence
  /\ succSet = [p \in Procs |-> [n \in Nodes |-> {}]]

(*----------------------------------------------------*)
(* Next-state relation (placeholder actions) *)
Next ==
  \/ \E p \in Procs:
        /\ pc[p] = "idle"
        /\ pc' = [pc EXCEPT ![p] = "work"]
        /\ sel' = [sel EXCEPT ![p] = << >>]
        /\ UNCHANGED <<marked, frontier, succSet>>
  \/ \E p \in Procs:
        /\ pc[p] = "work"
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ UNCHANGED <<marked, frontier, sel, succSet>>
  \/ \E p \in Procs:
        /\ pc[p] = "done"
        /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

(*----------------------------------------------------*)
(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*----------------------------------------------------*)
(* Invariant *)
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "work", "done"}]
  /\ sel \in [Procs -> Seq(Nodes)]
  /\ succSet \in [Procs -> [Nodes -> SUBSET Nodes]]

(*----------------------------------------------------*)
(* Refinement property (placeholder) *)
Refines == TRUE

(*----------------------------------------------------*)
(* Operator that replaces Succ in the configuration *)
ConnectedToSomeButNotAll(n) == Succ[n] \cap Nodes

(*----------------------------------------------------*)
(* Bounded version of Seq, replaces Seq in the configuration *)
LimitedSeq(T) == { s \in Seq(T) : Len(s) <= Cardinality(Nodes) }

====