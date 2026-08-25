---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------
  Finite version of the natural numbers used for model checking.
  The configuration replaces the standard Nat with NatOverride.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------
  State constraint: ticket numbers must stay strictly below MaxNat.
  This pruning ensures the finite NatOverride model remains sound.
-----------------------------------------------------------------*)
TicketBound == 
    /\ \A i \in 1..N : ticket[i] < MaxNat

(*-----------------------------------------------------------------
  Specification used by the model checker.
  It combines the original initialization and transition relation
  from the Boulanger specification with the state constraint.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ []TicketBound

(* The following identifiers are required by the .cfg file.
   They are defined in the Boulanger module; we simply expose them
   here so the configuration can refer to them directly. *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====