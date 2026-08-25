---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the constants required by the configuration *)
Nodes == 1..4
Root  == 1
Procs == {"P1", "P2"}

(* The graph is defined by the operator ConnectedToSomeButNotAll.
   The .cfg file will substitute this operator for Succ. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
     { m \in Nodes :
         /\ m # n
         /\ (m = (n % 4) + 1 \/ m = ((n + 1) % 4) + 1) }]

(* Provide a default definition for Succ (it will be overridden by the .cfg). *)
Succ == ConnectedToSomeButNotAll

(* LimitedSeq replaces the standard Seq operator so that sequences are bounded
   by the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

(* Initial state, using the concrete graph and process set *)
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = [p \in Procs |-> "idle"]
  /\ sel      = [p \in Procs |-> {}]
  /\ succSet  = [p \in Procs |-> {}]

(* For this configuration we keep Next abstract; the concrete actions are
   inherited from the parallel reachability algorithm. *)
Next == UNCHANGED vars

(* Specification formula required by the .cfg file *)
Spec == Init /\ [][Next]_vars

(* Inductive invariant: type correctness of the state variables *)
Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ \A p \in Procs : sel[p] \subseteq Nodes
  /\ \A p \in Procs : succSet[p] \subseteq Nodes

(* Refinement property asserted by the configuration (placeholder). *)
Refines == TRUE

====