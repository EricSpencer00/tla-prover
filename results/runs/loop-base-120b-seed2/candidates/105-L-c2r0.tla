---- MODULE DyadicRationals ----
EXTENDS Integers

(* Natural numbers as a subset of integers *)
Nat == { n \in Int : n >= 0 }

(* d is a power of two *)
PowerOfTwo(d) == \E k \in Nat : d = 2 ^ k

(* The set of dyadic rationals (numerator any integer, denominator a non‑zero power of two) *)
Dyadic == { [num |-> n, den |-> d] :
               n \in Int /\ d \in Nat /\ d # 0 /\ PowerOfTwo(d) }

(* The dyadic rational representing the value one *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization: repeatedly divide numerator and denominator by 2 while both are even *)
RECURSIVE Norm(_)

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLE p

(* Initial state: the dyadic rational one *)
Init == p = One

(* One step: halve the current value and then normalize it *)
Next == p' = Norm(Half(p))

(* Full specification *)
SPECIFICATION == Init /\ [][Next]_<<p>>

(* Invariant: the variable always denotes a dyadic rational *)
INVARIANTS == p \in Dyadic

(* Trivial property placeholder *)
PROPERTIES == TRUE

====