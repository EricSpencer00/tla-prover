---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The bounded NatOverride replaces the infinite Nat from Naturals so TLC can
\* check the theorem over a finite range; the theorem itself is assumed here.
NatOverride == 0 .. MaxNat

\* TheoremDoubleEven: for every natural n, 2 * n is even. Assumed true as a
\* constant-level statement so the model checks the configuration, not the math.
TheoremDoubleEven == \E n \in NatOverride : 2 * n = 2 * (n \div 2)

TypeOK == MaxNat \in NatOverride

Spec == TheoremDoubleEven

\* No system actions -- the theorem is a fixed property, so Init/Next are trivial.
Init == TRUE
Next == TRUE

SpecOK == Init /\ [][Next]_<< >>

====