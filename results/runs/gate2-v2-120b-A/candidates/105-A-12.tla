---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers, TLC

(***************************************************************************)
(* Constants (if any) can be declared here.  The description does not     *)
(* require external constants, so we leave this section empty.            *)
(***************************************************************************)

(***************************************************************************)
(* Identifier: One                                                          *)
(* Description: The dyadic rational representing the integer 1.            *)
(* Representation: A record with fields 'num' (numerator) and 'den'       *)
(* (denominator).                                                          *)
(***************************************************************************)
One == [num |-> 1, den |-> 1]

(***************************************************************************)
(* Identifier: Half                                                         *)
(* Description: The dyadic rational representing one half, i.e., 1/2.      *)
(* Representation: A record with numerator 1 and denominator 2.           *)
(***************************************************************************)
Half == [num |-> 1, den |-> 2]

(***************************************************************************)
(* Helper Definitions                                                       *)
(***************************************************************************)

(* Set of all dyadic rationals that we will consider.  The numerator is   *)
(* any integer, while the denominator is a positive integer that is a     *)
(* power of two.                                                            *)
DyadicSet == { [num |-> n, den |-> d] :
                n \in Int /\ d \in Nat \ {0} /\ \E k \in Nat : d = 2^k }

(***************************************************************************)
(* Identifier: Norm                                                         *)
(* Description: Normalization operator for dyadic rationals.  It repeatedly*)
(* divides both numerator and denominator by 2 while both are even,      *)
(* yielding a canonical form where at least one of them is odd.           *)
(***************************************************************************)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(***************************************************************************)
(* Variable Declaration                                                     *)
(***************************************************************************)
VARIABLES p

(***************************************************************************)
(* Init: the system may start in any dyadic rational (including One).      *)
(***************************************************************************)
Init ==
    /\ p \in DyadicSet

(***************************************************************************)
(* Next: two possible nondeterministic actions:                         *)
(*   1. Double the denominator (equivalent to multiplying the dyadic rational*)
(*      by 1/2).                                                            *)
(*   2. Normalize the current dyadic rational.                              *)
(***************************************************************************)
Next ==
    \/ /\ p' = [num |-> p.num, den |-> p.den * 2]   \* halve the value
    \/ /\ p' = Norm(p)                              \* reduce even factors

(***************************************************************************)
(* Specification: the standard temporal formula that the system must      *)
(* start in Init and forever satisfy the Next step.                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<p>>

(***************************************************************************)
(* INVARIANT: the denominator of the stored dyadic rational is always a   *)
(* power of two.  This invariant is maintained by both actions.           *)
(***************************************************************************)
DyadicDenPowerOfTwo ==
    \E k \in Nat : p.den = 2^k

(***************************************************************************)
(* PROPERTY (optional): the value represented by 'p' is always a rational*)
(* number between 0 (inclusive) and 2 (exclusive).  This follows from the*)
(* construction but is expressed as a simple sanity check.               *)
(***************************************************************************)
ValueRange ==
    0 <= p.num / p.den /\ p.num / p.den < 2

=============================================================================