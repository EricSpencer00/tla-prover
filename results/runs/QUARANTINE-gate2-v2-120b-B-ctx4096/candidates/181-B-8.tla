---- MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

\* The original specification asserted that MaxNat is NOT a natural number,
\* which caused a failure during model checking because the constant MaxNat
\* is later used to define the finite set NatOverride = 0 .. MaxNat.  In order
\* for NatOverride to be a well‑defined finite set, MaxNat must be a natural
\* number (or, more precisely, a non‑negative integer).  The intention of the
\* module is to model a bounded version of the natural numbers, so we replace
\* the contradictory assumption with a correct one that states MaxNat belongs
\* to Nat (the standard set of natural numbers).  This preserves the intended
\* semantics while allowing TLC to construct the required finite state space.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

\* Preserve the original assumption T1 (its definition resides in sums_even)
ASSUME T1
====================================================================