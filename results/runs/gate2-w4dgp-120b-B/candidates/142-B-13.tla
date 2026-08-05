---- MODULE ReachableProofs
(***************************************************************************)
(* This module contains the TLAPS checked proofs of partial correctness of *)
(* the algorithm in module Reachable, based on the invariants Inv1, Inv2,  *)
(* and Inv3 defined in that module.  The proofs here are simple: the heavy   *)
(* lifting is done in ReachabilityProofs.                                   *)
(*                                                                         *)
(* After writing the proof, I realized the invariants Inv2 and Inv3 could  *)
(* be replaced by the single invariant                                      *)
(*   Inv23 == Reachable = ReachableFrom(marked \cup vroot)                 *)
(* which is true initially and preserved by this general reachability       *)
(* result:                                                                  *)
(*   \A S \in SUBSET Nodes : \A n \in S : reachableFrom(S) = reachableFrom(S \cup Succ[n])  *)
(* Since marked \cup vroot only grows by adding successors of nodes in vroot. *)
(* The partial-correctness statement below follows from Inv1 and Inv23.     *)
(***************************************************************************)
EXTENDS Reachable, ReachabilityProofs, TLAPS

CONSTANTS Nodes, Succ
SuccAssump == Succ \in [Nodes -> SUBSET Nodes]
CONSTANT Root
RootAssump == Root \in Nodes

VARIABLES marked, vroot, pc
vars == <<marked, vroot, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ vroot \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ pc = "Done" => vroot = {}

Init ==
  /\ marked = {Root}
  /\ vroot = Succ[Root]
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF vroot # {}
       THEN /\ \E v \in vroot :
                 IF v \notin marked
                 THEN /\ marked' = marked \cup {v}
                      /\ vroot' = vroot \cup Succ[v]
                 ELSE /\ vroot' = vroot \ {v}
                      /\ UNCHANGED marked
            /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<marked, vroot>>

Next == a \/ UNCHANGED vars

Inv1 == pc = "Done" => vroot = {}
Inv2 == \A n \in marked : Succ[n] \subseteq marked
Inv3 == Reachable = marked \cup ReachableFrom(vroot)
Inv23 == Reachable = ReachableFrom(marked \cup vroot)

Spec == Init /\ [Next]_vars

THEOREM Thm1 == Spec => []Inv1
  <1>1. Init => Inv1 BY RootAssump, Init, Inv1, TypeOK
  <1>2. Inv1 /\ [Next]_vars => Inv1'
    <2> SUFFICES ASSUME Inv1, [Next]_vars PROVE Inv1' OBVIOUS
    <2>1. CASE a BY <2>1, SuccAssump, a, Inv1, TypeOK
    <2>2. CASE UNCHANGED vars BY <2>2, vars, Inv1
    <2>3. QED BY <2>1, <2>2, Next, Terminating
  <1>3. QED BY <1>1, <1>2, PTL, Spec

THEOREM Thm2 == Spec => []Inv2
  <1>1. Inv1 => Inv2 BY Reachable1, Inv1, Inv2, TypeOK
  <1> QED BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3
  <1>1. Init => Inv3 BY RootAssump, Init, Inv3, Reachable, TypeOK
  <1>2. TypeOK /\ Inv2 /\ Inv3 /\ [Next]_vars => Inv3'
    <2> SUFFICES ASSUME TypeOK, Inv2, Inv3, [Next]_vars PROVE Inv3' OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot)' = ReachableFrom(vroot')
          /\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
          OBVIOUS
    <2>2. CASE a
      <3>1. CASE vroot = {}
        BY <2>1, <3>1, Inv3, TypeOK
      <3>2. CASE vroot # {}
        PICK v \in vroot :
          IF v \notin marked
            THEN /\ marked' = marked \cup {v}
                 /\ vroot' = vroot \cup Succ[v]
            ELSE /\ vroot' = vroot \ {v}
                 /\ UNCHANGED marked
        BY <3>2
        <3>3. CASE v \notin marked
          <4>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
                /\ v \notin ReachableFrom(vroot)
              BY <3>2, <3>3, Reachable2, TypeOK
          <4>2. QED BY <4>1, <3>2, <3>3, Inv3, <2>1
        <3>4. CASE v \in marked
          <4>1. marked' \cup vroot' = marked \cup vroot BY <3>2, <3>4
          <4>2. QED BY <4>1, Inv2, Inv3, <2>1
        <3>5. QED BY <3>3, <3>4
    <2>3. CASE UNCHANGED vars BY <2>1, <2>3, Inv3, TypeOK, vars
    <2>4. QED BY <2>2, <2>3, Next, Terminating
  <1>3. QED BY <1>1, <1>2, Thm2, PTL, Spec

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  <1>1. Inv1 => (pc = "Done" => vroot = {})
    BY Inv1, TypeOK
  <1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3, Inv3
  <1>3. QED BY <1>1, <1>2, Thm1, Thm3, PTL, Spec
=============================================================================