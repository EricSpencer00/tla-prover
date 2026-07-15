---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers

CONSTANTS One, Half, Norm

(* ----------------------------------------------------------------------
   Record definition for a dyadic rational.
   We model a dyadic rational as a record with two fields:
     - num : the integer numerator
     - den : the positive integer denominator, a power of two
   The set of all such records is called Dyadics.
   ---------------------------------------------------------------------- *)
Dyadic == [num : Int, den : Nat]

Dyadics == { d \in Dyadic : d.den >= 1 /\ IsPowerOfTwo(d.den) }

IsPowerOfTwo(n) == 
    IF n = 1 THEN TRUE
    ELSE IF n % 2 # 0 THEN FALSE
    ELSE IsPowerOfTwo(n \div 2)

(* ----------------------------------------------------------------------
   The constant One represents the dyadic rational 1/1.
   Half represents the dyadic rational 1/2.
   ---------------------------------------------------------------------- *)
One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

(* ----------------------------------------------------------------------
   Norm(p) recursively divides numerator and denominator by two
   while both are even, yielding a reduced dyadic rational.
   ---------------------------------------------------------------------- *)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* ----------------------------------------------------------------------
   State variable representing the current dyadic rational.
   ---------------------------------------------------------------------- *)
VARIABLE x

(* ----------------------------------------------------------------------
   Initial state: the system starts with the dyadic rational One.
   ---------------------------------------------------------------------- *)
Init == x = One

(* ----------------------------------------------------------------------
   Next-state relation: at each step the system may either
     1. halve the current dyadic rational, or
     2. normalize the current dyadic rational.
   The halving operation builds a new record with the same numerator
   and a denominator doubled; the result is then normalized to keep
   the representation canonical.
   ---------------------------------------------------------------------- *)
Next ==
    \/ x' = Half * x
    \/ x' = Norm(x)

(* ----------------------------------------------------------------------
   Multiplication of a dyadic rational by a constant dyadic rational.
   We define it only for the constants used (Half and One).
   ---------------------------------------------------------------------- *)
Half * r == Norm([num |-> r.num, den |-> r.den * 2])

(* ----------------------------------------------------------------------
   Specification (temporal formula) required by the .cfg.
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<x>>

(* ----------------------------------------------------------------------
   The following operators are required by the task description,
   but they are not referenced in the .cfg.  They are provided for
   completeness and to avoid “unreferenced identifier” warnings.
   ---------------------------------------------------------------------- *)
OneOp == One
HalfOp == Half
NormOp(p) == Norm(p)

====