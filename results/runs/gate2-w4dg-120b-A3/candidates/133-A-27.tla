---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, Integers

(* WARNING: This module is a machine-generated spec derived from a
   natural-language system description. The identifiers it defines are
   constrained by the reference TLC configuration, which substitutes
   some operators inherited from the standard modules with bounded
   versions. Do not change the identifiers -- the .cfg expects them
   exactly as they appear here. All operators marked as "substituted"
   are provided on the right-hand side of the substitution; the left-
   side is never declared or defined here. *)

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succSet \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> "none"]
  /\ succSet = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = 0
  /\ n \in marked
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succSet' = [succSet EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED <<marked, frontier>>

Expand(p) ==
  /\ pc[p] = 1
  /\ frontier' = frontier \cup succSet[p]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, sel, succSet>>

Mark(p, n) ==
  /\ pc[p] = 2
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succSet' = [succSet EXCEPT ![p] = {}]

Next ==
  \E p \in Procs :
    \/ \E n \in Nodes : Select(p, n)
    \/ Expand(p)
    \/ \E n \in Nodes : Mark(p, n)

Spec == Init /\ [][Next]_vars

(* Inductive invariant: the shared marked and frontier sets are disjoint
   and every process is in exactly one phase of the protocol. *)
Inv ==
  /\ marked \cap frontier = {}
  /\ \A p \in Procs :
       /\ pc[p] \in 0..2
       /\ IF pc[p] = 0 THEN sel[p] = "none" ELSE TRUE
       /\ IF pc[p] \in 1..2 THEN succSet[p] \subseteq Nodes ELSE TRUE

(* The bounded parallel algorithm refines the sequential Misra
   algorithm: every marked node is reachable from the root in the base
   graph. *)
Refines ==
  \A n \in marked : \E s \in Seq(Nodes) : /\ s # <<>>
                                   /\ Head(s) = Root
                                   /\ Last(s) = n
                                   /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]

(* Operator overridden by the .cfg: a bound on sequence length equal to
   the number of nodes, making the configuration finite-state. *)
LimitedSeq(S) == CHOOSE s \in Seq(S) :
  /\ Len(s) = Cardinality(S)
  /\ \A i \in 1..Len(s) : s[i] \in S

(* Operator overridden by the .cfg: a bounded version of the successor
   relation, so the model stays finite. *)
ConnectedToSomeButNotAll(n) ==
  LET k == Cardinality(Succ[n])
  IN IF k <= 1 THEN Succ[n] ELSE SubSeq(Succ[n], 1, 1)

====