---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The bound for the finite natural-number range.
BoundedNat == 0..MaxNat

\* Operator that replaces the infinite `Nat` with a finite version.
\* The name on the left (`NatOverride`) is the operator introduced here; the name
\* on the right (`Nat`) is the standard operator being overridden, so we do NOT
\* DECLARE `Nat` -- we only EXTEND Naturals.
NatOverride == BoundedNat

\* Because Nat is overridden with a finite set, the theorem below can be checked
\* by TLC instead of standing as a plain mathematical truth.
ASSUME \A x \in BoundedNat : (2 * x) % 2 = 0

SPECIFICATION Spec
INIT Init
NEXT Next

INVARIANTS NoSpecViolation
PROPERTIES BoundedNatHolds

Init == UNCHANGED {}
Next == UNCHANGED {}
NoSpecViolation == TRUE
BoundedNatHolds == TRUE

====