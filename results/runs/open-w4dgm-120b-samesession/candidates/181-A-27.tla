---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

Spec == "BaseSpec"
MaxVal == MaxNat

ASSUME MaxVal \in Nat

VARIABLES base
vars == <<base>>

Init == base = 0

Incr == base < MaxVal /\ base' = base + 1
Next == Incr

SpecOK == Spec \in {"BaseSpec"}

SpecOKOnly == SpecOK /\ Init /\ [][Next]_vars

EvenDoubleSpec == SpecOKOnly

====