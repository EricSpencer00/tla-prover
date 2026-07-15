---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
    One,   \* the dyadic rational equal to 1/1
    Half,  \* the dyadic rational equal to 1/2
    Norm   \* normalization operator

(* ------------------------------------------------------------------- *)
(*  Types and records                                                   *)
(* ------------------------------------------------------------------- *)
VARIABLE p

(* A Dyadic rational is a record with integer numerator and denominator *)
Dyadic == [num : Int, den : Nat]

(* ------------------------------------------------------------------- *)
(*  Constants                                                            *)
(* ------------------------------------------------------------------- *)
One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

(* ------------------------------------------------------------------- *)
(*  Normalization operator                                               *)
(* ------------------------------------------------------------------- *)
(*  Norm(r) returns a dyadic rational that is equivalent to r but
    with no common factor 2 in numerator and denominator.  The definition
    is recursive: if both parts are even, divide them by two and recurse;
    otherwise return r unchanged. *)
Norm(r) ==
    IF r.num % 2 = 0 /\ r.den % 2 = 0
        THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
        ELSE r

(* ------------------------------------------------------------------- *)
(*  The system state                                                    *)
(* ------------------------------------------------------------------- *)
(*  The only mutable state is the current dyadic rational p. *)
Init ==
    p = One

(* ------------------------------------------------------------------- *)
(*  Actions                                                             *)
(* ------------------------------------------------------------------- *)
Halve ==
    /\ p = Norm([num |-> p.num, den |-> p.den * 2])
    /\ p' = Norm([num |-> p.num, den |-> p.den * 2])

Normalize ==
    /\ p' = Norm(p)
    /\ UNCHANGED << >>

Next ==
    \/ Halve
    \/ Normalize

(* ------------------------------------------------------------------- *)
(*  Specification                                                       *)
(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<p>>

(* ------------------------------------------------------------------- *)
(*  Invariant (optional but useful for sanity checking)                 *)
(* ------------------------------------------------------------------- *)
Inv ==
    /\ p.den > 0
    /\ p.num \* p.den >= 0   \* keep the sign consistent with the description

=============================================================================