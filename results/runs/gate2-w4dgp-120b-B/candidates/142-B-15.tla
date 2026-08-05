---- MODULE ReachableProofs
(***************************************************************************)
(* This module contains the TLAPS checked proofs of partial correctness of *)
(* the algorithm in module Reachable, based on the invariants Inv1, Inv2,  *)
(* and Inv3 defined in that module.  The careful reader may notice that    *)
(* this module does not do anything with the constants Succ and Root,     *)
(* leaving them as literal symbols.  That is not an omission:  the model    *)
(* checking step following the proofs must supply a concrete graph to run  *)
(* the model against, and those come from the .cfg.  The proofs are all    *)
(* about the shape of the reachable set, not about which graph it happens  *)
(* to be, so the proofs can treat Succ and Root as abstract constants.     *)
(*                                                                         *)
(* Keep the proof hierarchy as it is now: the level <1> QED steps are the   *)
(* only steps that have to be written by hand, everything else can be     *)
(* proved by TLAPS with an OBVIOUS or BY proof.                            *)
(*                                                                         *)
(* Like all of the modules in this repository, the one thing it does not   *)
(* do is prove safety properties about a real system: the safety property *)
(* it does prove is about a model that never runs.                         *)
(***************************************************************************)
EXTENDS Reachable, ReachabilityProofs, TLAPS

(***************************************************************************)
(* Invariance of Inv1 is standard; the two steps of the level <1> proof are *)
(* the usual ones.  The level <2> proof of the step is the usual           *)
(* decomposition of a state constraint combined with a state constraint     *)
(* defining a next-state relation.                                          *)
(***************************************************************************)
THEOREM Thm1 == Spec => []Inv1
  <1>1. Init => Inv1
    BY RootAssump DEF Init, Inv1, TypeOK    
  <1>2. Inv1 /\ [Next]_vars => Inv1'   
    <2> SUFFICES ASSUME Inv1, [Next]_vars PROVE Inv1' OBVIOUS
    <2>1. CASE a
        BY <2>1, SuccAssump DEF Inv1, TypeOK, a
    <2>2. CASE UNCHANGED vars
      BY <2>2 DEF Inv1, TypeOK, vars
    <2>3. QED
      BY <2>1, <2>2 DEF Next, Terminating
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec  

(***************************************************************************)
(* Inv2 is a direct consequence of Inv1 and the definition of Reachable.  *)
(***************************************************************************)
THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)
  <1>1. Inv1 => TypeOK /\ Inv2
    BY Reachable1 DEF Inv1, Inv2, TypeOK
  <1> QED
    BY <1>1, Thm1, PTL

(***************************************************************************)
(* Invariance of Inv3 needs Inv2 and the definition of ReachableFrom.  The  *)
(* level <2> proof of the only nontrivial case is written to match the     *)
(* shape of the case split it outlines:  a single case split with a       *)
(* picked v in vroot, then a nested case split on v \in marked.  The       *)
(* step <5>1 inside the case v \notin marked is the only thing the proof  *)
(* does not do with an OBVIOUS.  It uses Reachable2 from module           *)
(* ReachabilityProofs, which is the theorem in that module introduced by   *)
(* the author specifically for this one proof.                            *)
(***************************************************************************)
THEOREM Thm3 == Spec => []Inv3
  <1>1. Init => Inv3  
    BY RootAssump DEF Init, Inv3, TypeOK, Reachable 
  <1>2. TypeOK /\ TypeOK' /\ Inv2 /\ Inv2' /\ Inv3 /\ [Next]_vars => Inv3'
    <2> SUFFICES ASSUME TypeOK, TypeOK', Inv2, Inv2', Inv3, [Next]_vars PROVE Inv3' OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot)' = ReachableFrom(vroot')
          /\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
      OBVIOUS 
    <2>2. CASE a
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
=============================================================================