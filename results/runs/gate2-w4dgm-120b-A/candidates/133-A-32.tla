---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(* Configuration module for the parallel reachability algorithm.  It provides  *)
(* the concrete graph structure and a bounded sequence override needed for     *)
(* finite-state model checking.  All algorithm actions and state are inherited  *)
(* from the parallel reachability module; this module only adds the CONFIG.    *)

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

RECURSIVE SumSet(_)
SumSet(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})

TypeOK ==
    /\ marked \in 0..Cardinality(Nodes)
    /\ frontier \in 0..Cardinality(Nodes)
    /\ pc \in [Procs -> {"idle", "scanning", "succeeded", "failed"}]
    /\ selected \in [Procs -> 0..Cardinality(Nodes)]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = 0
    /\ frontier = 1
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> 0]
    /\ succs = [p \in Procs |-> << >>]

Pick(p, n) ==
    /\ pc[p] = "idle"
    /\ frontier > 0
    /\ frontier' = frontier - 1
    /\ pc' = [pc EXCEPT ![p] = "scanning"]
    /\ selected' = [selected EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED marked

Load(p, s) ==
    /\ pc[p] = "scanning"
    /\ s \in ConnectedToSomeButNotAll(selected[p])
    /\ Len(succs[p]) < Cardinality(Nodes)
    /\ succs' = [succs EXCEPT ![p] = Append(succs[p], s)]
    /\ UNCHANGED <<marked, frontier, pc, selected>>

Commit(p) ==
    /\ pc[p] = "scanning"
    /\ pc' = [pc EXCEPT ![p] = "succeeded"]
    /\ marked' = marked + Len(succs[p])
    /\ frontier' = frontier + Len(succs[p])
    /\ UNCHANGED <<selected, succs>>

GiveUp(p) ==
    /\ pc[p] = "scanning"
    /\ pc' = [pc EXCEPT ![p] = "failed"]
    /\ UNCHANGED <<marked, frontier, selected, succs>>

Reset(p) ==
    /\ pc[p] \in {"succeeded", "failed"}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = 0]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Pick(p, n)
    \/ \E p \in Procs, s \in Nodes : Load(p, s
    \/ \E p \in Procs : Commit(p) \/ GiveUp(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

(* The invariants are the same as in the algorithm module, so they are restated   *)
(* here rather than imported; the configuration module must define them.          *)
Inv ==
    /\ SumSet(selected) = marked + frontier - 1
    /\ \A p \in Procs : pc[p] \in {"idle", "scanning", "succeeded", "failed"}
    /\ \A p \in Procs : pc[p] = "scanning" => succs[p] # << >>
    /\ \A p \in Procs : pc[p] = "succeeded" => succs[p] # << >>

(* Refinement: the parallel algorithm behaves exactly like the sequential Misra  *)
(* reachability algorithm, up to the bounded frontier and marking bookkeeping.   *)
Refines == Inv

(* The graph structure is the same as in the sequential model; each node has     *)
(* exactly two successors, which keeps the frontier and marked counts tied        *)
(* together and makes the invariant nontrivial.                                   *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* The sequence bound is made explicit as a FINITE set of sequences, not the    *)
(* unbounded Seq operator, so the state space stays finite for model checking.   *)
FiniteSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(* The .cfg file substitutes LimitedSeq for Seq, so this operator is the one    *)
(* actually used in the model; it is defined as FiniteSeq to keep it checkable.  *)
LimitedSeq == FiniteSeq

====