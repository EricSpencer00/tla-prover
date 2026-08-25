---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Successor function used for model checking: each node has exactly two distinct successors. *)
ConnectedToSomeButNotAll(n) ==
  LET candidates == Nodes \ {n} IN
  CHOOSE S \in { S \in SUBSET candidates : Cardinality(S) = 2 } : TRUE

(* Finite version of Seq: sequences are bounded by the number of nodes. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Tuple of all state variables inherited from the parallel algorithm. *)
vars == <<marked, frontier, pc, chosen, succSet>>

(* Full specification: initial condition and next-state relation. *)
Spec == Init /\ [][Next]_vars

(* Simple type invariant for the state variables. *)
TypeInvariant ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> Nat]
  /\ chosen \in [Procs -> SUBSET Nodes]
  /\ succSet \in [Procs -> SUBSET Nodes]

Inv == TypeInvariant

(* Refinement property (placeholder for the actual refinement proof). *)
Refines == Spec

====