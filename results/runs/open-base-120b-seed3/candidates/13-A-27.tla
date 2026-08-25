---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Export the core definitions from the Bakery specification
Init == Bakery!Init
Next == Bakery!Next

MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

\* Inductive specification: any type‑correct state satisfying the invariant
\* may be an initial state, and the system must always follow Next.
ISpec == (Inv /\ [][Next]_vars)

====