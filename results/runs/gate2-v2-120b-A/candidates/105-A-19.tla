---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers

CONSTANTS
  One,          \* the dyadic rational representing 1
  Half,         \* the dyadic rational representing 1/2
  Norm          \* the normalization operator

(*-----------------------------------------------------------------
  Records representing dyadic rationals.
  Each record has two fields:
    - num : integer numerator (can be any integer)
    - den : positive integer denominator (always > 0)
-----------------------------------------------------------------*)
VARIABLE p

(*-----------------------------------------------------------------
  Set of all well‑formed dyadic rationals.
-----------------------------------------------------------------*)
Dyadic == { [num |-> n, den |-> d] : n \in Int, d \in Nat \ {0} }

(*-----------------------------------------------------------------
  One : the dyadic rational 1/1
-----------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]

(*-----------------------------------------------------------------
  Half : the dyadic rational 1/2
-----------------------------------------------------------------*)
Half == [num |-> 1, den |-> 2]

(*-----------------------------------------------------------------
  Norm : a recursive normalization function that divides numerator
         and denominator by 2 while both are even.
-----------------------------------------------------------------*)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  Initialization: the system starts with the value One.
-----------------------------------------------------------------*)
Init == p = One

(*-----------------------------------------------------------------
  Next: the system may either
        * halve the current dyadic rational,
        * normalize the result (which may be a no‑op if already normalized),
        * or stay in the same state.
-----------------------------------------------------------------*)
Next ==
  \/ /\ p' = [num |-> p.num, den |-> p.den * 2]               \* explicit halving step
        /\ p' = Norm(p')
  \/ /\ p' = Half                                            \* direct move to constant Half
        /\ p' = Norm(p')
  \/ /\ p' = p                                               \* stutter

(*-----------------------------------------------------------------
  Specification (the behavior of the system).
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*-----------------------------------------------------------------
  Invariant: the denominator is always positive (well‑formedness).
-----------------------------------------------------------------*)
Inv == p.den > 0

(*-----------------------------------------------------------------
  Property: the value of the dyadic rational is always between 0 and 2
            (inclusive).  This is a simple sanity check; it follows from
            the way the system evolves from One and never introduces
            numerators or denominators that would violate the bound.
-----------------------------------------------------------------*)
Prop == 0 <= p.num / p.den /\ p.num / p.den <= 2

====