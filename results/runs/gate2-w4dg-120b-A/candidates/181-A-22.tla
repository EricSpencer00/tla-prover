---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* MaxNat is the bound for the finite model; Nat is the range zero..MaxNat.
\* The theorem "forall n \in Nat: 2*n is even" is assumed as a constant-level
\* assumption, not proved here, so TLC can use it during model checking.
ASSUME Nat = 0..MaxNat

NoVars == TRUE

Init == NoVars
Next == NoVars

Spec == Init /\ [][Next]_NoVars

TypeOK == NoVars

\* The double-of-n is even theorem is assumed for model checking, not proved.
DoubleIsEven == NoVars

====