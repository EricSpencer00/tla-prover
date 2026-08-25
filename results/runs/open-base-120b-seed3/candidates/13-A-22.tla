---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* Include the original Bakery specification, using the same N constant
INSTANCE Bakery WITH N = N

\* Inductive specification: any type‑correct state satisfying the invariant can be initial,
\* and thereafter only the Bakery Next action is allowed.
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

\* Export the invariants defined in the Bakery module
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====