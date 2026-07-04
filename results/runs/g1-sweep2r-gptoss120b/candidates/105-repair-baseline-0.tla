---- MODULE DyadicRationals ----
(* Stub module for SANY parsing - provides dyadic rational operators *)
EXTENDS Integers

DyadicRational == [num : Int, den : Nat \ {0}]

Zero == [num |-> 0, den |-> 1]
One == [num |-> 1, den |-> 1]

IsDyadicRational(x) == x \in DyadicRational

Add(x, y) == [num |-> x.num * y.den + y.num * x.den, den |-> x.den * y.den]

Half(x) == [num |-> x.num, den |-> x.den * 2]

PrettyPrint(x) == x

====
