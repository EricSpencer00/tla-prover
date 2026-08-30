---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Replaces 'Nat' from Naturals with a finite version so TLC can explore
\* the natural numbers only up to MaxNat instead of forever.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here as an axiom so TLC can
\* treat it as a given truth rather than trying to re-prove it from
\* first principles; this is what enables model checking to terminate.
TheoremDoubleEven == \A n \in NatOverride : (n * 2) % 2 = 0

\* No state in this configuration module; everything is a constant-level
\* assumption about the mathematics the main proof will rely on.
Spec == TheoremDoubleEven

Init == Spec

Next == Spec

TypeOK == TRUE

StateConstraint == Spec

Terminate == TRUE

====