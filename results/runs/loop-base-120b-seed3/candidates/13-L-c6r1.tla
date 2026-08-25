---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite version of the natural numbers used by the model checker.
\*  The .cfg file will replace uses of Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\*  Export the invariants required by the .cfg file.
\* ----------------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

\* ----------------------------------------------------------------------
\*  Inductive specification: start from any type‑correct state satisfying
\*  the invariant, then enforce the next‑state relation forever.
\* ----------------------------------------------------------------------
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

====