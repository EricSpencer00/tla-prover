---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
    num, den, p

(* Values for the special operators *)
One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
        THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
        ELSE q

VARIABLES
    R

(* The set of all dyadic rationals, represented as records {num, den}
   with den > 0. *)
Dyadic == { [num |-> n, den |-> d] : n \in Integers /\ d \in Nat \ {0} }

Init ==
    /\ R = One

Next ==
    \/ (* Halve operation: double the denominator, keep numerator unchanged *)
       /\ R' = Half
    \/ (* Normalization step: divide both parts by two when both even *)
       /\ R.num % 2 = 0 /\ R.den % 2 = 0
       /\ R' = Norm([num |-> R.num \div 2, den |-> R.den \div 2])
    \/ (* Identity step: no change, to allow stuttering *)
       /\ R' = R

Spec == Init /\ [][Next]_<<R>>

(* No additional invariants or properties required by the .cfg,
   but they are defined for completeness. *)

Inv == R \in Dyadic

====