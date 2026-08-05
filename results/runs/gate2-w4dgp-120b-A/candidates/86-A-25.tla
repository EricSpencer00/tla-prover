---- MODULE TLAPS ----
EXTENDS Naturals

\* The Temporal Logic of Actions proof system accepts backend pragmas that
\* dispatch a proof obligation to a named prover.  The module below declares
\* those pragmas (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4)
\* as constant operators -- they carry no state and take no arguments -- but
\* their presence in the module reserves the names required by the TLAPS
\* configuration.  It also states the two fundamental theorems that every
\* proof in the library rests upon: set extensionality and the existence
\* of a value not in a given set.

CONSTANTS Zenon Isabelle CVC3 Yices VeriT Z3 SPASS LS4

\* Set extensionality: two sets with identical elements are equal.
Extensionality == \A x, y \in SUBSET Nat : (\A z \in Nat : (z \in x) <=> (z \in y)) => (x = y)

\* There is a value outside any given set of natural numbers.
ExistsOutside == \A x \in SUBSET Nat : \E y \in Nat : y \notin x

=============================================================================