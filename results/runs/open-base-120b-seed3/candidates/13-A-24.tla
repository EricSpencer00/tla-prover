---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* ----------------------------------------------------------------------
   Finite replacement for the (infinite) set of natural numbers.
   The model checker will substitute Nat with NatOverride.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   Invariants inherited from the Bakery specification.
   ---------------------------------------------------------------------- *)
MutualExclusion == Bakery.MutualExclusion
TypeOK          == Bakery.TypeOK
Inv             == Bakery.Inv

(* ----------------------------------------------------------------------
   Inductive specification: any type‑correct state satisfying the invariant
   may be an initial state, and the system evolves according to Next.
   ---------------------------------------------------------------------- *)
InitInductive == TypeOK /\ Inv

ISpec == InitInductive /\ [][Next]_vars

=============================================================================