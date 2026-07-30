---- MODULE MC_sums_even ----
EXTENDS Integers

CONSTANTS MaxNat, Nat

TypeOK ==
    /\ MaxNat \in Nat
    /\ Nat = 0..MaxNat

AssumeDoubleIsEven ==
    \A n \in Nat : 2 * n \in Nat /\ 2 * n \in Nat /\ (2 * n) % 2 = 0

Spec == Init /\ Next

Init ==
    /\ Nat = 0..MaxNat
    /\ MaxNat \in Nat
    /\ AssumeDoubleIsEven

Next == UNCHANGED <<Nat, MaxNat>>

Vars ==
    <<Nat, MaxNat>>

Spec_ ==
    Init /\ Next

SpecDef ==
    Spec

Init_ ==
    Init

Next_ ==
    Next

Invariants ==
    TypeOK

Properties ==
    AssumeDoubleIsEven
====