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
  BY DEF TypeOK, Safety, Next, Increment, Gossip, vars
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, vars

THEOREM Spec => Monotonicity
<1>1. TypeOK /\ [Next]_vars => [Monotonic]_vars
  BY DEF TypeOK, Safety, Next, Increment, Gossip, vars, Monotonic
<1>. QED  BY <1>1, TypeCorrect, PTL DEF Spec, Monotonicity, vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* Sum the values of a vector of natural numbers. We discharge the four    *)
(* Sum lemmas by reducing them to the corresponding `SumFunction` theorems *)
(* in the community-modules `FunctionTheorems`, via the trivial unfolding  *)
(*   Sum(f) = FoldFunction(+, 0, f)                                        *)
(*          = FoldFunctionOnSet(+, 0, f, DOMAIN f)                         *)
(*          = SumFunctionOnSet(f, DOMAIN f)                                *)
(*          = SumFunction(f).                                              *)
(***************************************************************************)
Sum(f) == FoldFunction(+, 0, f)

LEMMA SumIsSumFunction ==
  ASSUME NEW f
  PROVE  Sum(f) = SumFunction(f)
  BY DEF Sum, FoldFunction, SumFunction, SumFunctionOnSet

LEMMA SumType ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) \in Nat
  BY DEF Sum, FoldFunction

=============================================================================
