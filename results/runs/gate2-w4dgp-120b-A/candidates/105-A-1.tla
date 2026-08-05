---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES state

vars == <<state>>

Init == state = One

Next1 == state' = Half

Next2 == state' = Norm(state)

Next == Next1 \/ Next2

Spec == Init /\ [][Next]_vars

RationalIsNormalized == state.den >= 1 /\ state.den % 2 = 1

RationalValueIsOne == 2 * state.num = state.den

====