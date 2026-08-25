---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE p

(* ---------- Helper definitions ---------- *)

IsPowerOfTwo(d) == 
    IF d = 0 THEN FALSE
    ELSE (d = 1) \/ (d % 2 = 0 /\ IsPowerOfTwo(d \div 2))

Dyadic == { q \in [num : Int, den : Nat] : IsPowerOfTwo(q.den) }

(* ---------- Operator definitions ---------- *)

One == [num |-> 1, den |-> 1]

Half(q) == [num |-> q.num, den |-> q.den * 2]

RECURSIVE Norm(_)

Norm(q) == 
    IF q.num % 2 = 0 /\ q.den % 2 = 0 
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) 
    ELSE q

(* ---------- Specification ---------- *)

Init == p = One

Next == 
    \/ p' = Half(p)
    \/ p' = Norm(p)

Spec == Init /\ [][Next]_p

SPECIFICATION == Spec

INVARIANTS == 
    /\ p \in Dyadic

PROPERTIES == 
    TRUE

====