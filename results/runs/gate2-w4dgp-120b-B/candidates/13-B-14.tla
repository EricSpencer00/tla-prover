---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat
\* The original model used a numeric constant to bound the legroom (the
\* number of pizza-eaters the table can seat at once). That bound is intended
\* to be "big enough" -- not the thing being verified -- and a literal
\* (or a constant that must be instantiated as a literal by the config) is
\* what pushes the state space over TLC's horizon when the bound goes past
\* a dozen.
\*
\* TLAPS is fine with abstract ranges like "0..MaxNat" in a definition, so we
\* keep that here and only change the way the config is wired up: the constant
\* is still a name, but the config now has to give it a value, and the value
\* lives in the same Nat domain the model already uses (the Naturals
\* extension). That's the difference -- the config file itself drives the
\* bound being a numeric literal, not the module.
ASSUME MaxNat \notin Nat
NatOverride == 0 .. MaxNat
=============================================================================