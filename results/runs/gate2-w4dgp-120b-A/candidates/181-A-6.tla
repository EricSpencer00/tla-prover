---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == Nat \ { x \in Nat : x > MaxNat }

VARIABLES value, isEven

vars == <<value, isEven>>

Init ==
    /\ value = 0
    /\ isEven = TRUE

NextStep ==
    /\ value < MaxNat
    /\ value' = value + 1
    /\ isEven' = isEven
    /\ UNCHANGED isEven

DoubleStep ==
    /\ value = MaxNat
    /\ value' = 0
    /\ isEven' = TRUE
    /\ UNCHANGED isEven

Next ==
    \/ NextStep
    \/ DoubleStep

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(DoubleStep)

BoundedNat == (MaxNat \in 0..1000000)

====