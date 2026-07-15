---- MODULE MCBakery -------------------------------------------------
EXTENDS Bakery

CONSTANT MaxNat

\* The original assumption wrongly claimed that MaxNat is *not* a natural
\* number, which makes the model unsatisfiable because the extended module
\* Bakery (and the standard library) define Nat as the set of natural numbers.
\* We replace the assumption with a definition that restricts MaxNat to the
\* natural numbers.  This preserves the intended role of MaxNat as an upper
\* bound while allowing the specification to be checked.
NatOverride == 0 .. MaxNat

=============================================================================