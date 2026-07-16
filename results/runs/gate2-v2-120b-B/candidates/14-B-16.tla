--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger
CONSTANT MaxNat
\* Ensure MaxNat is a natural number (including 0). This makes the constant usable
\* as an upper bound for natural numbers without violating the semantics of the
\* operators that expect a natural number.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================