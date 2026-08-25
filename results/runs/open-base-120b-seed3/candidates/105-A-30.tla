---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Definition of dyadic rational records.
  A dyadic rational is a record with fields:
    num : integer numerator
    den : positive integer denominator that is a power of two
-----------------------------------------------------------------*)
Dyadic == [num : Int, den : Nat]

(* Helper predicate: true iff n is a power of two (n >= 1) *)
IsPowerOfTwo(n) == 
    /\ n >= 1
    /\ (n = 1) \/ (n % 2 = 0 /\ IsPowerOfTwo(n \div 2))

IsDyadic(p) == 
    /\ p \in Dyadic
    /\ IsPowerOfTwo(p.den)

(*-----------------------------------------------------------------
  Operator definitions required by the description
-----------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) == 
    IF p.num % 2 = 0 /\ p.den % 2 = 0 
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  Variables and actions for a minimal behavioural specification
-----------------------------------------------------------------*)
VARIABLE r

Init == r = One

Next == 
    \/ r' = Half(r)
    \/ r' = Norm(r)
    \/ UNCHANGED r

(*-----------------------------------------------------------------
  Standard top-level operators expected by the .cfg (even if empty)
-----------------------------------------------------------------*)
SPECIFICATION == Init /\ [] [Next]_<<r>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====