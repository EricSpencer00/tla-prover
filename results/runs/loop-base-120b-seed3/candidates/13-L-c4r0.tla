---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite replacement for the infinite set Nat used in the Bakery spec.
\*  The .cfg file substitutes Nat with NatOverride, therefore we provide
\*  a finite set of natural numbers ranging from 0 to MaxNat.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\*  Inductive specification: start from any state that satisfies the
\*  type invariant and then follow the Next relation forever.
\* ----------------------------------------------------------------------
ISpec == TypeOK /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Invariants required by the .cfg file.  They are simply re‑exported
\*  from the extended Bakery module.
\* ----------------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

====