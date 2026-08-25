---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite version of the natural numbers set, used to override Nat in the configuration.
NatOverride == 0 .. MaxNat

\* Bring in the original Bakery specification.
INSTANCE Bakery AS B

\* State variables, initial predicate and next-state relation are taken from Bakery.
Init == B!Init
Next == B!Next
vars == B!vars

\* Invariants inherited from Bakery.
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv

\* Inductive specification: start from any type‑correct state satisfying the invariant.
ISpec == (TypeOK /\ Inv) /\ [] ((TypeOK /\ Inv) /\ [Next]_vars)

====