---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm
CONSTANTS p

VARIABLES state

vars == <<state>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

TypeOK ==
  /\ state \in [num : Nat, den : Nat]
  /\ state.den \in {1, 2, 4}

Init ==
  state = One

Halve ==
  /\ state.den < 8
  /\ state' = Half
  /\ UNCHANGED p

Normalize ==
  /\ state.num % 2 = 0
  /\ state.den % 2 = 0
  /\ state' = Norm([num |-> state.num \div 2, den |-> state.den \div 2])
  /\ UNCHANGED p

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

====