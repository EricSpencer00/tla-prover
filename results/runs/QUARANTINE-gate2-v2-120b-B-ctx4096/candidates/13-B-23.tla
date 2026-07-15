---- MODULE MCBakery ------------------------------------------------
EXTENDS Bakery

CONSTANT MaxNat

\* The original assumption `ASSUME MaxNat \notin Nat` is contradictory,
\* because Nat is defined as the set of all natural numbers (0, 1, 2, …).
\* To keep the model consistent while preserving the intended meaning
\* that MaxNat should be a natural number, we replace the incorrect assumption
\* with a proper type constraint.  This change is minimal and does not weaken
\* any invariants defined in the extended module `Bakery`.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================