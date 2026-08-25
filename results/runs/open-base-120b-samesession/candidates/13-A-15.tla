---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Include the original Bakery specification
INSTANCE Bakery

\* Aliases for the core operators of the Bakery spec
INIT == Init
NEXT == Next

\* Inductive specification (starting from any state satisfying the invariant)
ISpec == Init /\ [][Next]_vars

====