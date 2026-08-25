---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

(* --------------------------------------------------------------------- *)
(*   Set of dyadic rationals: numerator is an integer, denominator a positive natural *)
Dyadic == { q \in [num : Int, den : Nat] : q.den > 0 }

(* --------------------------------------------------------------------- *)
(*   Constant representing the dyadic rational 1/1 *)
One == [num |-> 1, den |-> 1]

(* --------------------------------------------------------------------- *)
(*   Normalization operator: repeatedly divide numerator and denominator by 2
     while both are even *)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* --------------------------------------------------------------------- *)
(*   Halving operator: double the denominator and then normalize *)
Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

(* --------------------------------------------------------------------- *)
(*   State variables and actions for a simple system that starts at One
     and repeatedly halves the current value *)
INIT == p = One

NEXT == p' = Half(p)

SPECIFICATION == INIT /\ [][NEXT]_p

INVARIANTS == p \in Dyadic

PROPERTIES == SPECIFICATION

====