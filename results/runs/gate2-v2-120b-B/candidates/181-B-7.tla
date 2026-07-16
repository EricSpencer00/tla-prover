------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
\* The original specification assumed MaxNat \notin Nat, which makes the
\* model unsatisfiable because Nat contains all natural numbers.
\* To preserve the intended behavior while allowing the model to run,
\* we replace that assumption with a constraint that MaxNat is a natural
\* number greater than zero.  This keeps the module's semantics (the
\* range NatOverride is used to bound the natural numbers) but eliminates
\* the contradictory assumption.
ASSUME MaxNat \in Nat \ {0}
NatOverride == 0 .. MaxNat
ASSUME T1
====================================================================