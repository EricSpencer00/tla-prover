---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

(* ------------------------------------------------------------------- *)
(*  Bounded sequence operator – replaces the infinite Seq used in the   *)
(*  original algorithm.  It restricts sequence length to the number of *)
(*  nodes, guaranteeing a finite state space.                          *)
(* ------------------------------------------------------------------- *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ------------------------------------------------------------------- *)
(*  Successor relation used by the algorithm.  The .cfg substitutes     *)
(*  this operator for the original Succ, providing a concrete (finite) *)
(*  2‑successor mapping for each node.                                   *)
(* ------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) ==
  Succ[n]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* ------------------------------------------------------------------- *)
(*  Initialization – the algorithm starts with the root in the frontier *)
(*  and no nodes marked.                                                *)
(* ------------------------------------------------------------------- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

(* ------------------------------------------------------------------- *)
(*  Transition relation – a simple abstract version of the sequential *)
(*  reachability algorithm.                                            *)
(* ------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "start"
     /\ marked' = {}
     /\ frontier' = {Root}
     /\ pc' = "run"
  \/ /\ pc = "run"
     /\ IF frontier = {} THEN
          /\ marked' = marked
          /\ frontier' = {}
          /\ pc' = "done"
        ELSE
          LET n == Choose(frontier) IN
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ SetMinus marked')
          /\ pc' = "run"

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(*  Type correctness invariant                                           *)
(* ------------------------------------------------------------------- *)
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "run", "done"}

(* ------------------------------------------------------------------- *)
(*  Reachable set defined via bounded paths                           *)
(* ------------------------------------------------------------------- *)
Reachable ==
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

(* ------------------------------------------------------------------- *)
(*  Invariant 1 – successor closure                                      *)
(* ------------------------------------------------------------------- *)
Inv1 ==
  \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked

(* ------------------------------------------------------------------- *)
(*  Invariant 2 – marked set equals the set of reachable nodes           *)
(* ------------------------------------------------------------------- *)
Inv2 ==
  marked = Reachable

(* ------------------------------------------------------------------- *)
(*  Invariant 3 – frontier consists exactly of reachable nodes not yet  *)
(*               marked                                                *)
(* ------------------------------------------------------------------- *)
Inv3 ==
  frontier = Reachable \ marked

(* ------------------------------------------------------------------- *)
(*  Partial correctness – when the algorithm finishes, all reachable  *)
(*  nodes must be marked                                                *)
(* ------------------------------------------------------------------- *)
PartialCorrectness ==
  (frontier = {}) => (marked = Reachable)

(* ------------------------------------------------------------------- *)
(*  Liveness property – the algorithm eventually terminates            *)
(* ------------------------------------------------------------------- *)
Termination == <> (frontier = {})

====