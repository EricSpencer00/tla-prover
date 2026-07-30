---- MODULE MC_sums_even ----
EXTENDS Naturals

\* This model-checking configuration module for the proof that the double of any
\* natural number is even inherits the base proof specification and replaces the
\* unbounded natural-number set with a bounded range so TLC can explore it.
CONSTANTS
  MaxNat, Nat

\* SAFETY PROPERTY: the double of any natural number is even.  The property is
\* introduced as a top-level requirement for TLC, derived from the base proof.
EvenDouble(n) == (2 * n) % 2 = 0

\* Invariant: every reachable state satisfies that the double of any natural
\* number is even -- the theorem being model checked.
DoubleIsEven == \A n \in Nat : EvenDouble(n)

\* The set of natural numbers available to the current TLC run -- a finite range
\* from zero up to MaxNat, overriding the unbounded set in the base spec.
Nat == 0 .. MaxNat

\* The spec's full action set (Init, DoubleStep) comes from the base proof
\* specification, imported wholesale.  Not modeling any action of its own, this
\* module only adds the invariant being checked.
SPECIFICATION Spec
INIT Init
NEXT DoubleStep
INVARIANTS DoubleIsEven
PROPERTIES DoubleIsEven
====