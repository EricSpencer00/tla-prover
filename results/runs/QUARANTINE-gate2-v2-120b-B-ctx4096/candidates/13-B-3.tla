---- MODULE MCBakery -------------------------------------------------
EXTENDS Bakery

(* The original specification defined a constant MaxNat and then
   asserted `MaxNat \notin Nat`.  Since `Nat` is the set of all natural
   numbers (0,1,2,…), that assumption is never satisfiable, causing TLC
   to abort with a false assumption.  The intention, as indicated by
   the `NatOverride` definition, is to constrain MaxNat to be a natural
   number that serves as an upper bound for the overridden natural
   numbers used in the Bakery module.

   We therefore replace the unsatisfiable assumption with a proper
   constraint that MaxNat is a natural number.  This change is
   semantics‑preserving for the intended model: it still limits the
   range of natural numbers to `0..MaxNat` while allowing the model
   to be explored by TLC. *)
CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================