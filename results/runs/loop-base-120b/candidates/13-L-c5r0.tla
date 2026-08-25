---- MODULE MCBakery ----
EXTENDS Naturals, TLC
CONSTANT N, MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* Bring in the original Bakery specification
INSTANCE Bakery

\* Aliases for the required identifiers
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

\* Inductive specification used for model checking
ISpec == Init /\ [][Next]_vars

====