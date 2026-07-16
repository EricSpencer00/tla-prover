---- MODULE MCBakery ----
EXTENDS Bakery

\* The original specification assumed MaxNat was NOT a natural number,
\* which made the model checker immediately reject the module.
\* To keep the semantics of the Bakery algorithm while making the module
\* well‑formed, we remove that contradictory assumption and simply
\* require MaxNat to be a natural number.  The rest of the specification
\* (including the definition of NatOverride) remains unchanged.
CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================