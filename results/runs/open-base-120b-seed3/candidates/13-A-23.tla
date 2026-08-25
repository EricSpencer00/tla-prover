---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Expose the core components from the Bakery specification
Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

\* Invariants inherited from Bakery
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

\* Inductive specification: start from any TypeOK state and stay within Next
ISpec == 
    /\ TypeOK
    /\ [][Next]_vars

====