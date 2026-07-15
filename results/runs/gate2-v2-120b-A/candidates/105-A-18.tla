---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rationals are represented as records with fields:
    - num : the integer numerator
    - den : the positive integer denominator (a power of two)
  The set of all possible dyadic rationals is called Dyadics.
-----------------------------------------------------------------*)

Dyadic == [num : Int, den : Nat \ {0}]

Dyadics == { p \in Dyadic : IsPowerOfTwo(p.den) }

 (* Helper definition: a positive integer is a power of two *)
IsPowerOfTwo(d) == \E e \in Nat : d = 2 ^ e

ONE == [num |-> 1, den |-> 1]

Half(x) == [num |-> x.num, den |-> x.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES x

Init ==
  /\ x \in Dyadics
  /\ x = ONE

Next ==
  \/ /\ x' = Half(x)
     /\ x' \in Dyadics
  \/ /\ x' = Norm(x)
     /\ x' \in Dyadics

Spec == Init /\ [][Next]_<<x>>

(* The following operators are required by the .cfg, even if empty *)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====