---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANT N, MaxNat

\*-----------------------------------------------------------------
\* Finite override for the infinite set Nat
\*-----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\*-----------------------------------------------------------------
\* Aliases to definitions from the original Bakery module
\*-----------------------------------------------------------------
Vars == Bakery!Vars

INIT == Bakery!INIT
NEXT == Bakery!NEXT

\*-----------------------------------------------------------------
\* Inductive specification (starts from any type‑correct state)
\*-----------------------------------------------------------------
ISpec == TypeOK /\ [][NEXT]_Vars

\*-----------------------------------------------------------------
\* Invariants (simply re‑exposed from Bakery)
\*-----------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
=============================================================================