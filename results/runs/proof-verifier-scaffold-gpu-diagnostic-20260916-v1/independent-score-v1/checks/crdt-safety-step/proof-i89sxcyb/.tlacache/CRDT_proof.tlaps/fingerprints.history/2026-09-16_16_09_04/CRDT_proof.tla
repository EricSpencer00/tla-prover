------------------------------- MODULE CRDT_proof ---------------------------------
EXTENDS CRDT, Functions, NaturalsInduction, FunctionTheorems, TLAPS

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, Increment, Gossip, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec, vars


THEOREM Safe == Spec => []Safety
<1>1. Init => Safety
  BY DEF Init, Safety
<1>2. TypeOK /\ Safety /\ [Next]_vars => Safety'
  <1>2. TypeOK /\ Safety /\ [Next]_vars => Safety'
  BY DEF TypeOK, Next, Safety, vars
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, vars

=============================================================================
