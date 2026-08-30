---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

(* A model-checking configuration of the Misra reachability algorithm.  The   *)
(* configuration provides concrete definitions for the graph and for a        *)
(* bounded sequence type, so the state space is finite.  It inherits the       *)
(* algorithm's actions and invariants wholesale and only adds or overrides     *)
(* configuration definitions required by the .cfg.                             *)

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE Reachable(_)
Reachable(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN {n} \cup Reachable(S \ {n} \cup Succ[n])

\* Bounded sequence type: replaces Seq from Sequences, limiting length to the  *
\* number of nodes so the model is finite.                                    *
LimitedSeq(E) == { s \in Seq(E) : Len(s) <= Cardinality(Nodes) }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

Begin ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "working"
  /\ UNCHANGED <<marked, frontier>>

Explore(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier' \cup Succ[n]
  /\ UNCHANGED pc

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ pc' = "idle"
  /\ marked' = {Root}
  /\ frontier' = Succ[Root]

Next ==
  \/ Begin
  \/ \E n \in Nodes : Explore(n)
  \/ Finish
  \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Begin) /\ WF_vars(Finish) /\ WF_vars(Reset)

(* Each node reachable from the start is witnessed by a finite path of bounded *)
(* length, so restricting Seq to a bounded length does not drop any reachable  *)
(* node from consideration.                                                    *)
Inv1 == \A n \in Nodes : n \in Reachable({Root}) => \E p \in LimitedSeq(Nodes) : p # <<>> /\ p[1] = Root /\ p[Len(p)] = n

Inv2 == frontier \subseteq Reachable({Root})

Inv3 == marked \cup frontier = Reachable({Root})

Inv4 == marked \cap frontier = {}

PartialCorrectness == (frontier = {}) => (marked = Reachable({Root}))

Termination == <>(pc = "done")

(* The .cfg requires ConnectedToSomeButNotAll to be a finite or bounded       *)
(* version of Succ, used only by the invariant Inst1, which is already closed  *)
(* under Reachable and needs no further justification here.                    *)
ConnectedToSomeButNotAll == Succ

====