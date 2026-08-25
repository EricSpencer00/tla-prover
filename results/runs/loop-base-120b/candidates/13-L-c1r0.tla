---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N
CONSTANT MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* Bring in the original Bakery specification, binding the constants
INSTANCE Bakery WITH N = N, MaxNat = MaxNat

\* Inductive specification used for model checking
ISpec == Spec

====