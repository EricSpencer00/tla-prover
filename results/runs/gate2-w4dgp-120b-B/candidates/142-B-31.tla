---- MODULE ReachableProofs
/***************************************************************************
* This module contains the TLAPS checked proofs of partial correctness of  *
* the algorithm in module Reachable, based on the invariants Inv1, Inv2,   *
* and Inv3 defined in that module.  The proofs here are pretty simple,     *
* because the difficult parts involve proving general results about         *
* reachability that are independent of the algorithm.  Those results are   *
* stated and proved in module ReachabilityProofs and are used here.        *
*                                                                         *
* The algorithm is also covered by the unformalized but complete           *
* correctness argument at the end of the module.                          *
***************************************************************************)
EXTENDS Reachable, ReachabilityProofs, TLAPS

(***************************************************************************)
(* The invariance of TypeOK is implied by the invariance of Inv1, so there  *)
(* is no separate proof of it.                                              *)
(***************************************************************************)

(* Invariant Inv3 is equivalent to Inv2 /\ Inv23, where                     *)
(*     Inv23 == Reachable = ReachableFrom(marked \cup vroot)                *)
(* Inv23 is obvious initially and is kept true by the general result below   *)
(*   \A S \in SUBSET Nodes : \A n \in S : reachableFrom(S) = reachableFrom(S \cup Succ[n]) *
(* which applies to marked \cup vroot because it is only ever enlarged by   *
(* adding successors of nodes already in vroot.  Together with the           *
* invariance of Inv1, which says Reachable is closed under Succ, this gives  *
* the partial correctness conclusion that when vroot = {} all reachable    *
* nodes are in marked.                                                      *)
Inv23 == Reachable = ReachableFrom(marked \cup vroot)

THEOREM Thm1 == Spec => []Inv1
  <1>1. Init => Inv1
    BY RootAssump DEF Init, Inv1, TypeOK    
  <1>2. Inv1 /\ [Next]_vars => Inv1'   
    <2> SUFFICES ASSUME Inv1,
                        [Next]_vars
                 PROVE  Inv1'
      OBVIOUS
    <2>1. CASE a
        BY <2>1, SuccAssump DEF Inv1, TypeOK, a
    <2>2. CASE UNCHANGED vars
      BY <2>2 DEF Inv1, TypeOK, vars
    <2>3. QED
      BY <2>1, <2>2 DEF Next, Terminating
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec  

THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)
  <1>1. Inv1 => TypeOK /\ Inv2
    BY Reachable1 DEF Inv1, Inv2, TypeOK
  <1> QED
    BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3
  <1>1. Init => Inv3  
    BY RootAssump DEF Init, Inv3, TypeOK, Reachable 
  <1>2. TypeOK /\ TypeOK' /\ Inv2 /\ Inv2' /\ Inv3 /\ [Next]_vars => Inv3'
    <2> SUFFICES ASSUME TypeOK,
                        TypeOK',
                        Inv2,
                        Inv2',
                        Inv3,
                        [Next]_vars
                 PROVE  Inv3'
      OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot)' = ReachableFrom(vroot')   
          /\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
      OBVIOUS 
    <2>2. CASE a
      <3> USE <2>2 DEF a
      <3>1. CASE vroot = {}
        BY <2>1, <3>1 DEF Inv3, TypeOK
      <3>2. CASE vroot # {}
        <4>1. PICK v \in vroot :
                IF v \notin marked
                   THEN /\ marked' = (marked \cup {v})
                        /\ vroot' = vroot \cup Succ[v]
                   ELSE /\ vroot' = vroot \ {v}
                        /\ UNCHANGED marked
          BY <3>2
        <4>2. CASE v \notin marked
          <5>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
                /\ v \notin ReachableFrom(vroot)
            BY <4>1, <4>2, Reachable2 DEF TypeOK 
          <5>2. QED
            BY <5>1, <4>1, <4>2, <5>1, <2>1 DEF Inv3
        <4>3. CASE v \in marked
          <5>1. marked' \cup vroot' = marked \cup vroot
            BY <4>1, <4>3
          <5>2. QED
            BY <5>1, <2>1 DEF Inv2, Inv3
        <4>4. QED
          BY <4>2, <4>3
       <3>3. QED
          BY <3>1, <3>2   
    <2>3. CASE UNCHANGED vars
      BY <2>1, <2>3 DEF Inv3, TypeOK, vars  
    <2>4. QED
      BY <2>2, <2>3 DEF Next, Terminating
  <1>3. QED
    BY <1>1, <1>2, Thm2, PTL DEF Spec

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  <1>1. Inv1 => ((pc = "Done") => (vroot = {}))
    BY DEF Inv1, TypeOK
  <1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3 DEF Inv3  
  <1>3. QED
    BY <1>1, <1>2, Thm1, Thm3, PTL

(***************************************************************************
* The algorithm's correctness can also be covered by the following           *
* informal argument, which is equivalent to the theorems above.  The         *
* algorithm stops when vroot = {}.  By Invariant Inv2, this is exactly when *
* all reachable nodes are marked.  Invariant Inv1 says Reachable is closed  *
* under Succ, so marked is closed under Succ when vroot = {}, which by       *
* Reachable3 of module ReachabilityProofs means Reachable = Reachable      *
* (marked \cup ReachableFrom(vroot)) = marked.                             *
***************************************************************************)
=============================================================================