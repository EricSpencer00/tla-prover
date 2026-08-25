---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANT N
CONSTANT MaxNat

\*-----------------------------------------------------------------
\* Finite replacement for the infinite set Nat.
\* The model checker configuration replaces Nat with NatOverride.
\*-----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\*-----------------------------------------------------------------
\* Variables (inherited from Bakery)
\*-----------------------------------------------------------------
VARIABLES pc, ticket, choosing

\*-----------------------------------------------------------------
\* Initialization and next-state relation (delegated to Bakery)
\*-----------------------------------------------------------------
Init == Bakery!Init
Next == Bakery!Next

\*-----------------------------------------------------------------
\* Specification used for model checking (inductive specification)
\*-----------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

\*-----------------------------------------------------------------
\* Invariants (exposed from Bakery)
\*-----------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

====