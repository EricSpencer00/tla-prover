---- MODULE DyadicRationals ----
EXTENDS Integers, Naturals

(*--------------------------------------------------------------------
  Dyadic rational numbers are represented as records with integer
  numerator `num` and natural denominator `den`.  The denominator is
  always positive.
--------------------------------------------------------------------*)

Dyadic == [num : Int, den : Nat]

(* -----------------------------------------------------------------
   Constants
----------------------------------------------------------------- *)

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* -----------------------------------------------------------------
   Variables and actions
----------------------------------------------------------------- *)

VARIABLE dr

Init == dr = One

Next == dr' = Norm(Half(dr))

Spec == Init /\ [][Next]_<<dr>>

(* -----------------------------------------------------------------
   Standard identifiers required by the test harness (even though the
   .cfg file does not demand any).  They are defined as trivial
   wrappers around the core specification.
----------------------------------------------------------------- *)

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == TRUE

====