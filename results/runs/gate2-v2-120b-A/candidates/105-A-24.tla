---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers

(* ----------------------------------------------------------------------
   Dyadic rational representation
   Each dyadic rational is a record with fields:
     num : integer   (the numerator, can be any integer)
     den : Nat       (the denominator, a positive integer)
   The denominator is always a power of two.
   ---------------------------------------------------------------------- *)

VARIABLES p

(* --- Constants as required by the description --- *)
One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

(* ----------------------------------------------------------------------
   The normalization operator.
   It repeatedly halves the fraction while both numerator and denominator
   are even.  This yields a unique representation where at least one of
   the two numbers is odd (or the numerator is zero).
   ---------------------------------------------------------------------- *)
Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

(* ----------------------------------------------------------------------
   Well‑formed dyadic rationals: denominator is a positive power of two.
   ---------------------------------------------------------------------- *)
Dyadic(p) ==
  /\ p.den >= 1
  /\ \A i \in 0..(p.den - 1) : (2 ^ i) # p.den => p.den % (2 ^ i) # 0

(* ----------------------------------------------------------------------
   Initial state: the only initial dyadic rational is One, already
   normalized (which is trivially true).
   ---------------------------------------------------------------------- *)
Init ==
  p = One

(* ----------------------------------------------------------------------
   Next-state relation: from any dyadic rational p we may either
   1. Apply the halving constructor, which doubles the denominator,
      and then renormalize; or
   2. Apply the normalizing step itself (which may leave p unchanged).
   Both transitions keep the state within the set of well‑formed
   dyadic rationals.
   ---------------------------------------------------------------------- *)
Next ==
  \/ /\ p' = Norm([num |-> p.num, den |-> p.den * 2])
     /\ Dyadic(p')
  \/ /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
     /\ (p.num % 2 = 0 /\ p.den % 2 = 0)
     /\ Dyadic(p')
  \/ /\ p' = p               \* stuttering step to avoid deadlock
     /\ Dyadic(p')

(* ----------------------------------------------------------------------
   Specification operators required by the configuration
   (the .cfg does not demand any, but they are provided for completeness)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<p>>

(* ----------------------------------------------------------------------
   Optional auxiliary definitions that may be useful in the model checker
   ---------------------------------------------------------------------- *)
IsNormalized(q) == q = Norm(q)

THEOREM Spec => []Dyadic(p)

====