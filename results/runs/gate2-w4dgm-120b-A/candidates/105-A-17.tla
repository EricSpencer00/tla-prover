---- MODULE DyadicRationals ----
EXTENDS Integers

(* A dyadic rational is a fraction whose denominator is a power of two.  The  *)
(* module has a value "one", a "half" operator, and a recursive "Norm"       *)
(* that divides out a common factor of two from numerator and denominator.   *)

CONSTANTS One, Half, Norm

Operators == {"*", "\\"div", "%"}
EqualityOps == {"="}

RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

VARIABLES p
vars == <<p>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ p.den \in {1, 2, 4, 8}

Init ==
    /\ p = [num |-> 1, den |-> 1]

Spec ==
    /\ Init
    /\ [][Spec]_vars
    /\ WF_vars(p' = Half)

Spec ==
    /\ Init
    /\ [][Spec]_vars
    /\ WF_vars(p' = Half)

Half ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

DenPowerOfTwo ==
    \E k \in Nat : p.den = 2 ^ k

====