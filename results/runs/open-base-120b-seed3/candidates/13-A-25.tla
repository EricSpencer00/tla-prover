---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* ----------------------------------------------------------------------
   Finite version of the natural numbers used by the model checker.
   The .cfg file replaces Nat with NatOverride, so we provide a
   finite subset of Nat bounded by MaxNat.
   ---------------------------------------------------------------------- *)
NatOverride == { i \in Nat : i <= MaxNat }

(* ----------------------------------------------------------------------
   Bring in the full Bakery specification.  All definitions (variables,
   Init, Next, invariants, etc.) are available via the Bakery namespace.
   ---------------------------------------------------------------------- *)
INSTANCE Bakery

(* ----------------------------------------------------------------------
   Specification used for model checking (inductive specification).
   ---------------------------------------------------------------------- *)
ISpec == Bakery!Spec

(* ----------------------------------------------------------------------
   Invariants required by the configuration.
   ---------------------------------------------------------------------- *)
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

====