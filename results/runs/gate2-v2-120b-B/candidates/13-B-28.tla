---- MODULE MCBakery ----
EXTENDS Bakery

CONSTANT MaxNat

\* The original specification assumed that MaxNat is *not* a natural number,
\* which makes the model inconsistent and causes TLC to reject the model.
\* We replace that assumption with a consistent one that states MaxNat is a
\* natural number in the range used for overriding the built‑in Nat constant.
\* This preserves the intended semantics of `NatOverride` while allowing the
\* model to be checked.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

====