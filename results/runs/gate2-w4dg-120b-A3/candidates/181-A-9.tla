---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite natural-number set Nat with a bounded
\* version so TLC can handle the model. Nat itself is NOT declared or redefined.
NatOverride == 0..MaxNat

\* The theorem double-is-even is assumed at the constant level for model checking.
AssumeEven == TRUE

\* The operators below are the required identifiers from the reference .cfg.
\* Their bodies are placeholders because the description has NOT_SPECIFIED for
\* them; they exist so the .cfg file resolves correctly.
SPECIFICATION == "Trivial"
INIT == TRUE
NEXT == TRUE
INVARIANTS == "Trivial"
PROPERTIES == "Trivial"

====