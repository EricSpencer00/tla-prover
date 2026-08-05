---- MODULE DyadicRationals ----
EXTENDS Integers
CONSTANTS One, Half, Norm
VARIABLES p
vars == <<p>>
Spec == One
Init == p = One
Next == p' = Norm([num |-> p.num, den |-> p.den * 2])
Inv == p.den \in {1, 2, 4, 8}
Prop == Half = Norm([num |-> 1, den |-> 2])
TypeOK == /\ p \in [num : 0..10, den : {1, 2, 4, 8}]
          /\ Half \in [num : 0..10, den : {1, 2, 4, 8}]
          /\ One \in [num : 0..10, den : {1, 2, 4, 8}]
          /\ Spec \in [num : 0..10, den : {1, 2, 4, 8}]
          /\ \A c \in {One, Half, Norm} : c \in [num : 0..10, den : {1, 2, 4, 8}]
Init == p = Spec
Next == p' = Norm([num |-> p.num, den |-> p.den * 2])
Inv == p.den \in {1, 2, 4, 8}
====