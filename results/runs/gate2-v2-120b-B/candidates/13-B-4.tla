---- MODULE MCBakery ----------------------------------------------------
EXTENDS Bakery

\* The original specification incorrectly assumed that MaxNat is *not* a natural
\* number, which caused the model checker to fail because the assumption was
\* immediately false.  The intention of the module is to allow the modeler to
\* choose any natural number (including 0) as the upper bound for the set that
\* overrides the default natural numbers used by the Bakery module.
\* Therefore we replace the contradictory assumption with a harmless one that
\* simply states that MaxNat is a natural number.  This preserves the original
\* semantics (MaxNat can be any natural) while enabling the model to be checked.

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=====================================================================