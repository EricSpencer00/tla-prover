---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK == /\ p \in Nat \X Nat
          /\ One \in Nat \X Nat
          /\ Half \in Nat \X Nat

Init == p = One

Next == /\ p' = Norm(p)
        /\ UNCHANGED <<One, Half>>

Spec == Init /\ [][Next]_vars

HalfProp == p = Half

====