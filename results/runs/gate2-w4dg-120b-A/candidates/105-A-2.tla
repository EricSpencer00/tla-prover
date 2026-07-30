---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is represented as a record with a numerator and a denominator.
\* The system normalizes fractions by repeatedly dividing both parts by two whenever
\* they are both even.
CONSTANT One
CONSTANT Half
CONSTANT Norm
CONSTANT Specification
CONSTANT Init
CONSTANT Next
CONSTANT TypeOK
CONSTANT ValuesAreDyadic

Specification ==
    /\ Init /\ [][Next]_Specification
    /\ TypeOK
    /\ ValuesAreDyadic

Init ==
    Specification = One

Next ==
    Specification' = Half \/ Specification' = Norm(Specification)

TypeOK ==
    /\ Specification \in [num : Int, den : Int]

ValuesAreDyadic ==
    (Specification.num * 1) / Specification.den \in Nat

One == [num |-> 1, den |-> 1]

Half == [num |-> Specification.num, den |-> Specification.den * 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

====