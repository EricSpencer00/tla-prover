---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* ----------------------------------------------------------------------
   Finite version of the natural numbers set, used by the .cfg replacement
   of Nat with NatOverride.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   State constraint: every process's ticket number must stay strictly below
   the configured maximum.  This prunes states that would require numbers
   outside the finite NatOverride range.
   ---------------------------------------------------------------------- *)
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

(* ----------------------------------------------------------------------
   Specification for model checking.  It reuses the Init and Next
   definitions from the Boulanger specification and adds the state
   constraint defined above.
   ---------------------------------------------------------------------- *)
Spec == Init /\ [] (Next /\ TicketBound)

====