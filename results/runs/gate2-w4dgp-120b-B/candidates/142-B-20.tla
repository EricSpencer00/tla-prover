---- MODULE ReachableProofs
(* This module contains the TLAPS checked proofs of partial correctness of
   the algorithm in module Reachable, based on the invariants Inv1, Inv2,
   and Inv3 defined in that module.  The proofs here are pretty simple
   because the difficult parts involve proving general results about
   reachability that are independent of the algorithm; those results are
   stated and proved in module ReachabilityProofs and are used by the
   proofs in this module.

   After writing the proof, it occurred to me that it might be easier to
   replace invariants Inv2 and Inv3 by the single invariant

       Inv23 == Reachable = ReachableFrom(marked \cup vroot)

   which is invariant by the general result

       \A S \in SUBSET Nodes : \A n \in S : reachableFrom(S) = reachableFrom(S \cup Succ[n])

   since marked \cup vroot is changed only by adding successors of nodes
   in vroot to it.  Partial correctness is then true because when vroot
   is empty, Inv1 guarantees that every marked node has its successors
   marked, and Inv23 reduces to Reachable = reachableFrom(marked), which
   holds for any set of nodes all of whose successors are inside it.

   As an exercise, you can try rewriting the proof of partial correctness
   using only the invariants Inv1 and Inv23, using the same reachability
   results.  When you're done, you can try proving those reachability
   results. *)
EXTENDS Reachable, ReachabilityProofs, TLAPS

THEOREM Thm1 == Spec => []Inv1
  (* The three level <1> steps and its QED step's proof are the same for
     any inductive invariance proof.  Step <1>2 is the only one that TLAPS
     couldn't prove with a BY. *)
  <1>1. Init => Inv1
    BY RootAssump DEF Init, Inv1, TypeOK
  <1>2. Inv1 /\ [Next]_vars => Inv1'
    <2> SUFFICES ASSUME Inv1, [Next]_vars PROVE Inv1'
      OBVIOUS
    <2>1. CASE a BY <2>1, SuccAssump DEF Inv1, TypeOK, a
    <2>2. CASE UNCHANGED vars BY <2>2 DEF Inv1, TypeOK, vars
    <2>3. QED BY <2>1, <2>2 DEF Next, Terminating
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)
  (* A trivial consequence of a general fact about reachability in a
     directed graph. *)
  <1>1. Inv1 => TypeOK /\ Inv2
    BY Reachable1 DEF Inv1, Inv2, TypeOK
  <1> QED BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3
  (* Hierarchical reading: read all the steps of a level, then read the
     proof of each, starting with the QED step.  Observe how the
     invariance of TypeOK and Inv2 are used in the invariance of Inv3. *)
  <1>1. Init => Inv3  
    BY RootAssump DEF Init, Inv3, TypeOK, Reachable
  <1>2. TypeOK /\ TypeOK' /\ Inv2 /\ Inv2' /\ Inv3 /\ [Next]_vars => Inv3'
    <2> SUFFICES ASSUME TypeOK, TypeOK', Inv2, Inv2', Inv3, [Next]_vars
                 PROVE Inv3' OBVIOUS
    <2>1. /\ Reachable' = Reachable
          /\ ReachableFrom(vroot') = ReachableFrom(vroot')
          /\ ReachableFrom(marked \cup vroot)' = ReachableFrom(marked' \cup vroot')
      OBVIOUS
    <2>2. CASE a
      <3>1. CASE vroot = {}
        BY <2>1, <3>1 DEF Inv3, TypeOK
      <3>2. CASE vroot # {}
        <4>1. PICK v \in vroot :
                IF v \notin marked
                  THEN /\ marked' = marked \cup {v}
                       /\ vroot' = vroot \cup Succ[v]
                  ELSE /\ vroot' = vroot \ {v}
                       /\ UNCHANGED marked
          BY <3>2
        <4>2. CASE v \notin marked
          <5>1. /\ ReachableFrom(vroot') = ReachableFrom(vroot)
                /\ v \notin ReachableFrom(vroot)
            BY <4>1, <4>2, Reachable2 DEF TypeOK
          <5>2. QED BY <5>1, <4>1, <4>2, <5>1, <2>1 DEF Inv3
        <4>3. CASE v \in marked
          <5>1. marked' \cup vroot' = marked \cup vroot
            BY <4>1, <4>3
          <5>2. QED BY <5>1, <2>1 DEF Inv2, Inv3
        <4>4. QED BY <4>2, <4>3
       <3>3. QED BY <3>1, <3>2   
    <2>3. CASE UNCHANGED vars BY <2>1, <2>3 DEF Inv3, TypeOK, vars
    <2>4. QED BY <2>2, <2>3 DEF Next, Terminating
  <1>3. QED BY <1>1, <1>2, Thm2, PTL DEF Spec

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  (* Follows from Inv1 and Inv3 and the trivial Reachable3: Reachable({})
     equals {}. *)
  <1>1. Inv1 => ((pc = "Done") => (vroot = {}))
    BY DEF Inv1, TypeOK
  <1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3 DEF Inv3
  <1>3. QED BY <1>1, <1>2, Thm1, Thm3, PTL

====