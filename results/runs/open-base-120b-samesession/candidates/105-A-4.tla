---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

(* --- Constants --- *)
One == [num |-> 1, den |-> 1]

(* --- Operators --- *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* --- Specification scaffolding (required identifiers) --- *)
INIT == p = One

NEXT == p' = Half(p)

SPECIFICATION == INIT /\ [][NEXT]_p

INVARIANTS == TRUE

PROPERTIES == TRUE

====