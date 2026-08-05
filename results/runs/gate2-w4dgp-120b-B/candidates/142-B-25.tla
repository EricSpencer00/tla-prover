---- MODULE ReachableProofs
(***************************************************************************)
(* This module contains the TLAPS checked proofs of partial correctness of *)
(* the algorithm in module Reachable, based on the invariants Inv1, Inv2,  *)
(* and Inv3 defined in that module.  The proofs here are pretty simple     *)
(* because the difficult parts involve proving general results about       *)
(* reachability that are independent of the algorithm.  Those results are  *)
(* stated and proved in module ReachabilityProofs and are used by the      *)
(* proofs in this module.                                                  *)
(*                                                                         *)
(* You might be sufficiently motivated to make sure the algorithm is       *)
(* correct to want a machine-checked proof that is, but not motivated      *)
(* enough to write machine-checked proofs of the properties of directed    *)
(* graphs that the proof uses.  If that's the case, or you're curious      *)
(* about why it might be the case, read module ReachabilityTest.           *)
(*                                                                         *)
(* After writing the proof, it occurred to me that it might be easier to   *)
(* replace inv3 by a single invariant that is obviously true initially and *)
(* invariant:                                                              *)
(*                                                                         *)
(*    inv3  == reachable = reachableFrom(marked \cup vroot)                *)
(*                                                                         *)
(* since marked \cup vroot is changed only by adding successors of nodes   *)
(* in vroot to it, and a node is added to marked only once.  Partial        *)
(* correctness then follows from a couple of standard results about        *)
(* reachability: (1) reachableFrom(S) = reachableFrom(S \cup Succ[n]) for   *)
(* any n in S, and (2) S = reachableFrom(S) whenever every node in S has    *)
(* its successors in S.                                                     *)
(*                                                                         *)
(* (Having the smaller invariant inv3 instead of inv2 and inv3 is the       *)
(* reason the above comment is in the module's opening comment block, rather*)
(* than a separate note.)                                                  *)
(***************************************************************************)
EXTENDS Reachable, ReachabilityProofs, TLAPS

(***************************************************************************)
(* Inv1's TypeOK is the module's only type-correctness check, and its       *)
(* invariance is what lets the rest of the proof assume TypeOK without     *)
(* stating it again.                                                       *)
(***************************************************************************)

THEOREM thm1 == Spec => []Inv1
  <1>1. Init => Inv1
    BY RootAssump DEF Init, Inv1, TypeOK
  <1>2. Inv1 /\ [Next]_vars => Inv1'
    <2> SUFFICES ASSUME Inv1, [Next]_vars PROVE Inv1' OBVIOUS
    <2>1. CASE a BY <2>1, SuccAssump DEF Inv1, TypeOK, a
    <2>2. CASE UNCHANGED vars BY <2>2 DEF Inv1, TypeOK, vars
    <2>3. QED BY <2>1, <2>2 DEF Next, Terminating
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM thm2 == Spec => [](TypeOK /\ inv2)
  <1>1. Inv1 => TypeOK /\ inv2
    BY Reachable1 DEF Inv1, inv2, TypeOK
  <1> QED BY <1>1, thm1, PTL

THEOREM thm3 == Spec => []inv3
  <1>1. Init => inv3
    BY RootAssump DEF Init, inv3, Reachable
  <1>2. TypeOK /\ inv2 /\ inv3 /\ [Next]_vars => inv3'
    <2> SUFFICES ASSUME TypeOK, inv2, inv3, [Next]_vars PROVE inv3' OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot') = ReachableFrom(vroot')
          /\ ReachableFrom(marked \cup vroot') = ReachableFrom(marked \cup vroot')
      OBVIOUS
    <2>2. CASE a
      <3>1. CASE vroot = {}
        BY <2>1, <3>1 DEF inv3, TypeOK
      <3>2. CASE vroot # {}
        <4>1. PICK v \in vroot : IF v \notin marked
                     THEN /\ marked' = marked \cup {v}
                          /\ vroot' = vroot \cup Succ[v]
                     ELSE /\ vroot' = vroot \ {v}
                          /\ UNCHANGED marked
          BY <3>2
        <4>2. CASE v \notin marked
          <5>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
                /\ v \notin ReachableFrom(vroot)
            BY <4>1, <4>2, Reachable2 DEF TypeOK
          <5>2. QED BY <5>1, <4>1, <4>2, <5>1, <2>1 DEF inv3
        <4>3. CASE v \in marked
          <5>1. marked' \cup vroot' = marked \cup vroot
            BY <4>1, <4>3
          <5>2. QED BY <5>1, <2>1 DEF inv2, inv3
        <4>4. QED BY <4>2, <4>3
      <3>3. QED BY <3>1, <3>2
    <2>3. CASE UNCHANGED vars
      BY <2>1, <2>3 DEF inv3, TypeOK, vars
    <2>4. QED BY <2>2, <2>3 DEF Next, Terminating
  <1>3. QED BY <1>1, <1>2, thm2, PTL

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  <1>1. Inv1 => ((pc = "Done") => (vroot = {}))
    BY DEF Inv1
  <1>2. inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3 DEF inv3
  <1>3. QED BY <1>1, <1>2, thm1, thm3, PTL
=============================================================================