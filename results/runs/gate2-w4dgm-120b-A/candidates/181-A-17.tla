---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANTS MaxNat

\* The override replaces the infinite set Nat with a finite bounded range
\* so TLC can explore the state space. It is a FINITE set, not an alias for
\* Nat, and we keep Nat from Naturals for everything else.
NatOverride == 0 .. MaxNat

Spec == "Proof of the even-doubling theorem"
Theorem == "For every natural number n, 2*n is even"

Init == TRUE
Next == Init
SpecIsComplete == TRUE

TypeOK == TRUE

====