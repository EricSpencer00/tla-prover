---- MODULE ReachableProofs --------------------------
EXTENDS Reachable, ReachabilityProofs, TLAPS

(***************************************************************************)
(* This module contains the TLAPS checked proofs of partial correctness of*)
(* the algorithm in module Reachable, based on the invariants Inv1, Inv2, *)
(* and Inv3 defined in that module.  The proofs here are simple because   *)
(* the difficult parts involve proving general results about reachability*)
(* that are independent of the algorithm.  Those results are stated and  *)
(* proved in module ReachabilityProofs and are used by the proofs in this*)
(* module.                                                                 *)
(***************************************************************************)

THEOREM Thm1 == Spec => []Inv1
  <1>1. Init => Inv1
    BY Init, Inv1
  <1>2. Inv1 /\ [Next]_vars => Inv1'
    OBVIOUS
  <1>3. QED
    BY <1>1, <1>2, PTL

THEOREM Thm2 == Spec => [](TypeOK /\ Inv2)
  <1>1. Inv1 => TypeOK /\ Inv2
    BY Reachable1, Inv1, Inv2, TypeOK
  <1>2. QED
    BY <1>1, Thm1, PTL

THEOREM Thm3 == Spec => []Inv3
  <1>1. Init => Inv3
    BY Init, Inv3, TypeOK, Reachable
  <1>2. TypeOK /\ Inv2 /\ Inv3 /\ [Next]_vars => Inv3'
    OBVIOUS
  <1>3. QED
    BY <1>1, <1>2, Thm2, PTL

THEOREM Spec => []((pc = "Done") => (marked = Reachable))
  <1>1. Inv1 => ((pc = "Done") => (vroot = {}))
    BY Inv1, TypeOK
  <1>2. Inv3 /\ (vroot = {}) => (marked = Reachable)
    BY Reachable3, Inv3
  <1>3. QED
    BY <1>1, <1>2, Thm1, Thm3, PTL
=============================================================================