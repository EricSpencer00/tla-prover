---- MODULE Reachable ----
(* 2024-08-08 12:00:00.0 *)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* Reachable is the set of nodes reachable from Root *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

(* ------------------------------------------------------------------------- *)
(*  Initial state                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ vroot  = {Root}
    /\ pc     = "a"

(* ------------------------------------------------------------------------- *)
(*  Action a: the algorithm's main step.                                      *)
(*  The original spec omitted an explicit update to pc, causing TLC to       *)
(*  complain.  The fix adds a deterministic pc update:                       *)
(*    * if the loop continues, pc stays "a";                                 *)
(*    * when the loop finishes (vroot empty), pc becomes "Done".            *)
(* ------------------------------------------------------------------------- *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED <<marked, vroot>>
          ELSE /\ \E v \in vroot:
                ( IF v \notin marked
                     THEN /\ marked' = marked \cup {v}
                          /\ vroot'  = vroot  \cup Succ[v]
                          /\ pc'     = "a"
                     ELSE /\ marked' = marked
                          /\ vroot'  = vroot \ {v}
                          /\ pc'     = "a" )
               /\ UNCHANGED pc

(* ------------------------------------------------------------------------- *)
(*  Termination stuttering step (no variable changes)                        *)
(* ------------------------------------------------------------------------- *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, vroot, pc>>

Next ==
    \/ a
    \/ Terminating

vars == <<marked, vroot, pc>>

Spec ==
    Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(*  Type correctness invariant                                               *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* ------------------------------------------------------------------------- *)
(*  Invariant Inv1 (original)                                               *)
(* ------------------------------------------------------------------------- *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked: Succ[n] \subseteq (marked \cup vroot)

(* ------------------------------------------------------------------------- *)
(*  Invariant Inv2 (original)                                               *)
(* ------------------------------------------------------------------------- *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* ------------------------------------------------------------------------- *)
(*  Invariant Inv3 (original)                                               *)
(* ------------------------------------------------------------------------- *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* ------------------------------------------------------------------------- *)
(*  Partial correctness theorem (uses Inv3 and TypeOK)                      *)
(* ------------------------------------------------------------------------- *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

(* ------------------------------------------------------------------------- *)
(*  Liveness theorem: termination when Reachable is finite                 *)
(* ------------------------------------------------------------------------- *)
THEOREM ASSUME IsFiniteSet(Reachable) PROVE Spec => <>(pc = "Done")

====