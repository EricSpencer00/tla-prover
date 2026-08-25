---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set Nat
NatOverride == 0 .. MaxNat

\* Inductive specification: any state satisfying TypeOK may be an initial state,
\* and all reachable states respect the Next action.
ISpec == /\ TypeOK
        /\ [][Next]_vars

SPECIFICATION == ISpec
====