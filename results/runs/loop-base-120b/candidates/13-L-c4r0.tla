---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Include the original Bakery specification
INSTANCE Bakery

\* Re‑export state variables tuple used by the Bakery spec
vars == Bakery!vars

\* Re‑export the basic actions
Init == Bakery!Init
Next == Bakery!Next

\* Inductive specification: start from any type‑correct state and
\* enforce the next‑state relation forever
TypeOK == Bakery!TypeOK
ISpec == TypeOK /\ [][Next]_vars

\* Invariants required by the .cfg file
MutualExclusion == Bakery!MutualExclusion
Inv == Bakery!Inv

====