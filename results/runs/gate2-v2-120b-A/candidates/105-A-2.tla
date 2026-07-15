---- MODULE DyadicRationals ----
EXTENDS Integers

(* ----------------------------------------------------------------------
   Constants (none required by the .cfg, but we keep this section for
   completeness; they are not used elsewhere)
   ---------------------------------------------------------------------- *)

CONSTANTS

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)

Dyadic == [num : Int, den : Nat]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

IsPositiveDen(d) == d > 0

(* ----------------------------------------------------------------------
   Operator definitions required by the description
   ---------------------------------------------------------------------- *)

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Recursive normalization: keep dividing numerator and denominator by 2
   while both are even.  The recursion is expressed via a fixed‑point
   operator using TLC's recursion support. *)
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)

VARIABLE p

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

Init ==
  /\ p \in Dyadic
  /\ p.num = 1
  /\ p.den = 1
  /\ IsPositiveDen(p.den)

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)

Next ==
  \/ /\ p' = Half(p)
     /\ IsPositiveDen(p'.den)
  \/ /\ p' = Norm(p)
     /\ IsPositiveDen(p'.den)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
  Init /\ [][Next]_<<p>>

(* ----------------------------------------------------------------------
   Invariant: after any number of steps the denominator is always positive
   ---------------------------------------------------------------------- *)

DenPositive == IsPositiveDen(p.den)

(* ----------------------------------------------------------------------
   Optional: a type invariant (useful for model checking but not required)
   ---------------------------------------------------------------------- *)

TypeOK == p \in Dyadic /\ IsPositiveDen(p.den)

=============================================================================