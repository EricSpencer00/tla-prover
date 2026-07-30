---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm
CONSTANTS Specification
CONSTANTS Init
CONSTANTS Next
CONSTANTS Invariants
CONSTANTS Properties

P == [num : Int, den : Int]

Specification == [One |-> [num |-> 1, den |-> 1], Half |-> [num |-> 1, den |-> 2], Norm |-> (x) : IF x.num % 2 = 0 /\ x.den % 2 = 0 THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2]) ELSE x]

Init == [val |-> One]

Next == [val |-> Half]

Invariants == [valExists |-> TRUE]

Properties == [normReducesEven |-> TRUE]
====