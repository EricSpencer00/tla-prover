---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

Spec == /\ p = One
        /\ p.num \in Nat /\ p.den \in Nat

Init(p0) == /\ p.num = p0.num /\ p.den = p0.den
            /\ p0.num \in Nat /\ p0.den \in Nat

Next(p0, p1) == /\ p = p1 /\ p1 = Half(p0)

Invariants == TRUE
Properties == TRUE
====