---- MODULE MCBakery --------------------------------
EXTENDS Bakery

\* The original specification incorrectly assumed that MaxNat is not a natural number,
\* which caused TLC to fail because the assumption is trivially false when MaxNat
\* is intended to be used as an upper bound for a natural number range.
\* We replace the false assumption with a correct one that states MaxNat is a natural
\* number.  This preserves the intended semantics of the module while allowing the
\* model checker to proceed.

CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================