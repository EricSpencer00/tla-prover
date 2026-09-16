------------------------------- MODULE CRDT_proof ---------------------------------
EXTENDS CRDT, Functions, NaturalsInduction, FunctionTheorems, TLAPS

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <1>3. TypeOK /\ [Next]_vars => TypeOK'
  BY <1>1, <1>2, <1>1, <1>2
<1>. QED  BY <1>1, <1>2, PTL DEF Spec, vars

=============================================================================
