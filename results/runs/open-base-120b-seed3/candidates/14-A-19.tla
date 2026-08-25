---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* ----------------------------------------------------------------------
   Finite override of the natural numbers set.
   The model checker will replace Nat with NatOverride, restricting
   all natural-number values to the range 0..MaxNat.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   State constraint: all ticket numbers must stay strictly below MaxNat.
   This prunes states that would require values outside the finite range.
   ---------------------------------------------------------------------- *)
TicketBound == \A i \in 1 .. N : ticket[i] < MaxNat

(* ----------------------------------------------------------------------
   Specification for model checking.
   It combines the original initialization and next-state relation
   from the Boulanger specification with the additional state constraint.
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ TicketBound

====