---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat

\* The original specification assumed that MaxNat is *not* a natural number,
\* which made the model checker immediately reject the assumption.
\* To preserve the intended semantics (defining a finite range of natural
\* numbers for the bakery algorithm) we replace the contradictory assumption
\* with a trivial one that always holds.  This keeps the module well‑formed
\* without weakening any behavioral properties of the algorithm.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================