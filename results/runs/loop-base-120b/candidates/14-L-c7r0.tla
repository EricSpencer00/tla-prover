---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N
CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* The overall specification (initial condition and next‑state relation)
Spec == Init /\ [][Next]_vars

====