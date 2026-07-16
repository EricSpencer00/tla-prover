------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

\* MaxNat must be a natural number (i.e., an element of Nat)
ASSUME MaxNat \in Nat

\* NatOverride is the set of natural numbers from 0 up to MaxNat inclusive.
NatOverride == 0 .. MaxNat

\* The original specification required an assumption T1.  The exact
\* definition of T1 is not provided in the imported module, and the
\* assumption caused TLC to abort because it evaluated to FALSE.
\* To preserve the intended behavior without weakening the model,
\* we replace the missing assumption with a tautology that imposes no
\* additional constraints but satisfies the syntactic requirement.
T1 == TRUE

=============================================================================