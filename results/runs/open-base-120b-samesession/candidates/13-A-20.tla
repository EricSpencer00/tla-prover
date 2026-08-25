---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite replacement for the infinite set Nat. *)
NatOverride == 0 .. MaxNat

(* Inductive specification: start from any type‑correct state and
   require that every step respects the Next relation. *)
ISpec == TypeOK /\ [][Next]_vars

====