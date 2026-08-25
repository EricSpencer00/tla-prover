---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------
  Finite replacement for the infinite set Nat.
  The .cfg file will replace Nat with NatOverride, so all uses of Nat
  in the inherited Boulanger specification become 0..MaxNat.
-----------------------------------------------------------------*)
NatOverride == 0..MaxNat

(*-----------------------------------------------------------------
  State‑constraint: all ticket numbers must stay strictly below MaxNat.
-----------------------------------------------------------------*)
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

(*-----------------------------------------------------------------
  Specification: the original Init and Next from Boulanger together
  with the state‑constraint.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next /\ TicketBound]_vars

(*-----------------------------------------------------------------
  Invariants inherited from Boulanger.
-----------------------------------------------------------------*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====