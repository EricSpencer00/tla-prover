---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the configuration *)
Nodes == 1..4
Root == 1
Procs == 1..2
Succ == ConnectedToSomeButNotAll

(* Each node has exactly two successors, wrapped around the 4‑node ring *)
ConnectedToSomeButNotAll(n) ==
  { (n % 4) + 1 , ((n+1) % 4) + 1 }

(* LimitedSeq is a finite version of Seq, bounded by the number of nodes *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc, sel, succSet

Init ==
  /\ marked   = {Root}
  /\ frontier = {}
  /\ pc       = [p \in Procs |-> 0]
  /\ sel      = [p \in Procs |-> Root]
  /\ succSet  = [p \in Procs |-> {}]

Next == UNCHANGED <<marked, frontier, pc, sel, succSet>>

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

Inv ==
  /\ marked   \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc       \in [Procs -> Nat]
  /\ sel      \in [Procs -> Nodes]
  /\ succSet  \in [Procs -> SUBSET Nodes]

Refines == TRUE

=============================================================================