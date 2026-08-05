---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend provers available to the TLA Proof System (TLAPS).
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* The timeout (in seconds) after which a prover run is abandoned.
CONSTANTS Timeout

\* Each identifier below is a TLAPS pragma naming a prover and the tactic
\* (or configuration) with which to invoke it. The notation ::Pragma:: is
\* recognized by the proof system and has no operational effect in the
\* model itself.

\* Isabelle backed by the Zenon prover.
NoZenon == ::Zenon "nozenon"::Timeout

\* Isabelle backed by the Z3 prover.
NoZ3 == ::Z3 "noz3"::Timeout

\* Isabelle backed by the veriT prover.
NoVeriT == ::veriT "noverit"::Timeout

\* Isabelle backed by the LS4 temporal prover, with a hard clause limit.
NoLS4 == ::LS4 "nol4"::Timeout::"hard"::10

\* Isabelle backed by the SPASS prover.
NoSPASS == ::SPASS "nospass"::Timeout

\* Isabelle backed by the CVC3 prover.
NoCVC3 == ::CVC3 "nocvc3"::Timeout

\* Isabelle backed by the Yices prover.
NoYices == ::Yices "noyices"::Timeout

\* Isabelle backed by the builtin first-order prover.
NoIsabelle == ::Isabelle "noisabelle"::Timeout

\* Isabelle backed by the built-in propositional prover.
NoProp == ::Isabelle "noprop"::Timeout

SetExtensionality ==
  \A x \in {x \in {x \in {}} : x \in {}} : x = x

NoSetContainsAll ==
  \A x \in {x \in {x \in {}} : TRUE} : TRUE

====