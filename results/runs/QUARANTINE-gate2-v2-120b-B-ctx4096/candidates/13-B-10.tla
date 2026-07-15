---- MODULE MCBakery --------------------------------
EXTENDS Bakery

\* The original specification incorrectly assumed that MaxNat is not a natural
\* number, which caused TLC to immediately reject the model because the
\* assumption could never be satisfied.  The intention of the module is to
\* provide a finite set of natural numbers that can be used as an override for
\* the natural numbers in the Bakery module.  Therefore we replace the faulty
\* assumption with a harmless one that simply states that MaxNat is a natural
\* number.  This change preserves the intended semantics (a finite range of
\* naturals) while allowing the model to be checked.

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

====