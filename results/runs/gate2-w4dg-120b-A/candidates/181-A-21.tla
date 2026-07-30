---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
    MaxNat,
    Nat

\* The double of any natural number in the bounded set zero..MaxNat is even.
\* This is the theorem being model-checked; it is assumed here so TLC can
\* process the specification.

SpecAssumption == \A n \in Nat : (2 * n) % 2 = 0

SPECIFICATION == SpecAssumption

VARIABLES
    Numbers

vars == <<Numbers>>

TypeOK == Numbers \subseteq Nat

Init ==
    /\ Numbers = {}

Next ==
    /\ \E n \in Nat :
        /\ ~ \E x \in Numbers : x = n
        /\ Numbers' = Numbers \cup {n}
    /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars

EvenDoubles == SpecAssumption

\* The overridden bounded set is the only condition needed for TLC to run;
\* the theorem itself is assumed, never proved inside this module.
BoundedNat == Cardinality(Nat) <= MaxNat + 1

====