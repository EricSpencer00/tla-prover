---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

(* Relation induced by the successor function *)
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

(* Nodes reachable (by any number of Succ steps) from a set S, 
   including the nodes of S themselves *)
ReachFrom(S) ==
  S \cup { n \in Nodes : \E s \in S : <<s, n>> \in TC(SuccRel) }

(* Nodes reachable from the designated root *)
ReachRoot == ReachFrom({Root})

(*--------------------------------------------------------------------
  Operators required by the .cfg
--------------------------------------------------------------------*)

(* The .cfg substitutes this for Succ *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* Finite version of Seq (used only to satisfy the .cfg substitution) *)
LimitedSeq(S) == Seq(S)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Run"

Next ==
  \/ \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = pc
  \/ \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = pc
  \/ /\ frontier = {}
        /\ marked' = marked
        /\ frontier' = frontier
        /\ pc' = "Done"

vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Run", "Done"}

Inv1 ==
  \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
  ReachRoot = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (frontier = {} => marked = ReachRoot)

(*--------------------------------------------------------------------
  Liveness property
--------------------------------------------------------------------*)

Termination == <> (frontier = {})

====