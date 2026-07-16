---- MODULE MCBakery --------------------------------
EXTENDS Bakery

\* The standard Naturals module defines Nat = 1.., which does not include 0.
\* To model a bounded space of natural numbers that includes 0, we define
\* NatOverride as a finite set of numbers from 0 up to (and including) MaxNat.
\* MaxNat is assumed to be a natural number (i.e., a non‑negative integer) that
\* is not already an element of Nat. This assumption guarantees that 0..MaxNat
\* is a non‑empty, finite set distinct from the infinite Nat set.

CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================