---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* ----------------------------------------------------------------------
   Finite version of the natural numbers.
   The .cfg file replaces Nat with NatOverride, limiting tickets to 0..MaxNat.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   Specification used by the model checker.
   ---------------------------------------------------------------------- *)
ISpec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Optional wrappers required by the configuration.
   ---------------------------------------------------------------------- *)
INIT == Init
NEXT == Next

(* ----------------------------------------------------------------------
   Set of invariants that the model checker must verify.
   ---------------------------------------------------------------------- *)
INVARIANTS == { MutualExclusion , TypeOK , Inv }

(* ----------------------------------------------------------------------
   No additional liveness properties are specified.
   ---------------------------------------------------------------------- *)
PROPERTIES == {}

====