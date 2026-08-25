---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE p

(* --- Operators --- *)

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* --- Specification components --- *)

Init == p = One

Next ==
  \/ p' = Half(p)
  \/ p' = Norm(p)

SPECIFICATION == Init /\ [][Next]_<<p>>

INIT == Init

NEXT == Next

INVARIANTS == TRUE

PROPERTIES == TRUE

====