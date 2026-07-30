---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  noZero, noTime

ASSUME noZero \notin Naturals

RECURSIVE Extensional(_)
Extensional(S) ==
  IF \E x \in S : TRUE
  THEN LET x == CHOOSE y \in S : TRUE
           T == {y \in S : y /= x /\ Extensional({y})}
       IN IF x \in S THEN S = {x} \cup T ELSE S = T
  ELSE S = {}

INVARIANTS ==
  { Extensional, \A S \in SUBSET Naturals : \E u \in S : \E v \in S : u = v }

VARIABLES
  zenon, isabelle, cvc3, yices, verit, z3, spass, ls4, tactics, timeout

vars == << zenon, isabelle, cvc3, yices, verit, z3, spass, ls4, tactics, timeout >>

TypeOK ==
  /\ zenon \in {noZero}
  /\ isabelle \in {noZero}
  /\ cvc3 \in {noZero}
  /\ yices \in {noZero}
  /\ verit \in {noZero}
  /\ z3 \in {noZero}
  /\ spass \in {noZero}
  /\ ls4 \in {noZero}
  /\ tactics \in SUBSET Nat
  /\ timeout \in Nat

Init ==
  /\ zenon = noZero
  /\ isabelle = noZero
  /\ cvc3 = noZero
  /\ yices = noZero
  /\ verit = noZero
  /\ z3 = noZero
  /\ spass = noZero
  /\ ls4 = noZero
  /\ tactics = {}
  /\ timeout = noTime

Next ==
  /\ \E p \in {zenon, isabelle, cvc3, yices, verit, z3, spass, ls4} :
       \E v \in {noZero} : p' = v
  /\ \E n \in Nat : timeout' = n
  /\ \E T \in SUBSET Nat : tactics' = T
  /\ UNCHANGED << zenon, isabelle, cvc3, yices, verit, z3, spass, ls4 >>

SpecWAIT == TRUE

Spec == SpecWAIT

====