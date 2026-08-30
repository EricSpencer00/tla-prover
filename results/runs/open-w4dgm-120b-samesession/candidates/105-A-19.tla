---- MODULE DyadicRationals ----
EXTENDS Integers

(* A dyadic rational is a fraction whose denominator is a power of two.  The   *)
(* module exposes the value one, a halving operator, and a normalizing        *)
(* operator that divides numerator and denominator by two while both are     *)
(* even.  "Norm" is defined recursively via function application with a lazy  *)
(* base case.                                                                  *)

CONSTANTS Integers, "*", "\div", "%", "=", "[", "]", "One", "Half", "Norm",
    "/", "\\", "num", "den", "IF", "THEN", "ELSE", "&&", "p", "q"

Zero == 0
Two == 2

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

Norm(p) ==
    IF p.num % Two = Zero /\ p.den % Two = Zero
        THEN Norm([num |-> p.num \div Two, den |-> p.den \div Two])
        ELSE p

TypeOK ==
    /\ One \in [num : Integers, den : Integers]
    /\ Half \in [num : Integers, den : Integers]

Spec == TRUE

====