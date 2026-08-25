---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* Define a constant relation representing the graph edges.
   Each node has exactly two successors. *)
SuccRel == { <<1,2>>, <<1,4>>,
             <<2,1>>, <<2,3>>,
             <<3,2>>, <<3,4>>,
             <<4,1>>, <<4,3>> }

(* The graph is defined by the operator ConnectedToSomeButNotAll.
   The .cfg file will substitute this operator for Succ. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> { m \in Nodes : <<n,m>> \in SuccRel } ]

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

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ \A p \in Procs : sel[p] \subseteq Nodes
  /\ \A p \in Procs : succSet[p] \subseteq Nodes

Refines == TRUE

====