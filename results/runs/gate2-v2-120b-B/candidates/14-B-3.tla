---- MODULE MCBoulanger ----
EXTENDS Boulanger

\* The original specification declared a constant MaxNat that was assumed not to be a natural
\* number, but later used MaxNat as an upper bound for a set of natural numbers. This makes the
\* assumption contradictory and causes TLC to abort.  We keep the constant, but change the
\* assumption so that MaxNat is a natural number and, therefore, can serve as a legitimate upper
\* bound for the overridden natural numbers.
CONSTANT MaxNat

\* MaxNat must be a natural number (an element of Nat) and must be at least 1 so that the set
\* NatOverride = 0..MaxNat is non‑empty and useful.
ASSUME MaxNat \in Nat \ {0}

NatOverride == 0 .. MaxNat

\* StateConstraint ensures that for every process the associated counter stays strictly below the
\* configured maximum.
StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================