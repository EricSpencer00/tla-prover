---- MODULE MCBakery ----
EXTENDS Naturals, TLC
CONSTANT N, MaxNat

\* Finite replacement for the infinite set of natural numbers
NatOverride == 0 .. MaxNat

\* State variables that will be linked to the Bakery specification
VARIABLES pc, unchecked, nxt, flag

\* Bring in the original Bakery specification, providing the required parameters
INSTANCE Bakery WITH
    num       <- N,
    max       <- MaxNat,
    pc        <- pc,
    unchecked <- unchecked,
    nxt       <- nxt,
    flag      <- flag

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