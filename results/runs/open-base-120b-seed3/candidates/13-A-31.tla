---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set Nat
NatOverride == 0 .. MaxNat

\* Tuple of all state variables defined in the Bakery specification
\* (adjust the list if the Bakery module introduces additional variables)
Vars == <<choosing, number>>

\* Inductive specification: any state satisfying TypeOK is an allowed initial
\* state, and the system must always stay TypeOK while taking steps described by Next
ISpec == TypeOK /\ [] (TypeOK /\ [Next]_Vars)

====