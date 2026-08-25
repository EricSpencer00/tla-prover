---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers set, used to override Nat in the configuration.
NatOverride == 0 .. MaxNat

\* Bring in the original Bakery specification.
INSTANCE Bakery

\* State variables, initial predicate and next-state relation are taken from Bakery.
Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

\* Invariants inherited from Bakery.
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

\* Inductive specification: start from any type‑correct state satisfying the invariant.
ISpec == (TypeOK /\ Inv) /\ [] ((TypeOK /\ Inv) /\ [Next]_vars)

====