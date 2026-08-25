---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE dr

(* The set of dyadic rational records *)
Dyadic == {[num : Int, den : Nat] : den > 0}

(* The dyadic rational representing one *)
One == [num |-> 1, den |-> 1]

(* Halve a dyadic rational by doubling its denominator *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalize a dyadic rational by removing common factors of two *)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* Initial state: the rational value is one *)
INIT == dr = One

(* Possible next-state transitions *)
NEXT ==
    \/ dr' = Half(dr)
    \/ dr' = Norm(dr)
    \/ dr' = dr

(* The overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<dr>>

(* Invariant: the variable always denotes a dyadic rational *)
INVARIANTS == dr \in Dyadic

(* Trivial property placeholder *)
PROPERTIES == TRUE

====