---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Constants (not used directly but listed for completeness)
-----------------------------------------------------------------*)
CONSTANTS
  One,        \* the dyadic rational representing 1
  Half,       \* the dyadic rational representing 1/2
  Norm        \* the normalization operator

(*-----------------------------------------------------------------
  State variable
-----------------------------------------------------------------*)
VARIABLE p

(*-----------------------------------------------------------------
  Record constructor shortcuts (for readability)
-----------------------------------------------------------------*)
OneVal == [num |-> 1, den |-> 1]
HalfVal == [num |-> 1, den |-> 2]

(*-----------------------------------------------------------------
  Normalization operator
-----------------------------------------------------------------*)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ p = OneVal
  /\ p = One        \* ensure the constant name One denotes this value

(*-----------------------------------------------------------------
  Next-state relation (the only evolution is optional halving)
-----------------------------------------------------------------*)
Next ==
  \/ /\ p.num % 2 = 0
        /\ p.den % 2 = 0
        /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  \/ /\ p' = p

(*-----------------------------------------------------------------
  Specification (temporal formula)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*-----------------------------------------------------------------
  (Optional) invariants and properties – none required by the .cfg
-----------------------------------------------------------------*)
\* Invariant stating that denominator is always a positive power of two
DenPowerOfTwo ==
  \A n \in Nat :
    (p.den = 2 ^ n)

=============================================================================