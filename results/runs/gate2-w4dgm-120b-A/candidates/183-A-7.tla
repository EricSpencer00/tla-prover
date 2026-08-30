---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

SpecVersion == 1

DispatchTo(zenon) == SpecVersion
DispatchTo(isabelle) == SpecVersion
DispatchTo(cvc3) == SpecVersion
DispatchTo(yices) == SpecVersion
DispatchTo(sert) == SpecVersion
DispatchTo(z3) == SpecVersion
DispatchTo(spass) == SpecVersion
DispatchTo(ls4) == SpecVersion

Extensionality == \A X, Y \in SUBSET Nat : (\A x \in X : x \in Y) /\ (\A y \in Y : y \in X) => X = Y

NoSetContainsAllValues == \A X \in SUBSET Nat : X # Nat

Spec == Extensionality /\ NoSetContainsAllValues

====