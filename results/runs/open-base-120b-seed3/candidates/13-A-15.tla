---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* Import the original Bakery specification
INSTANCE Bakery AS B

\* Export the state variables set used by the original spec
vars == B!vars

\* Export the initialization and next-state actions
Init == B!Init
Next == B!Next

\* Invariants required by the configuration
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv

\* Inductive specification: start from any type‑correct state
ISpec == TypeOK /\ [][Next]_vars

====