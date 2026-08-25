---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite replacement for the infinite set of natural numbers.
NatOverride == 0 .. MaxNat

\* Specification used by the TLC configuration.
ISpec == Init /\ [][Next]_vars

====