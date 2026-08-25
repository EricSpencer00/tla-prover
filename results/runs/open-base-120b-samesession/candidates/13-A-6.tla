---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(* Finite version of Nat, to be used via the .cfg replacement *)
NatOverride == 0 .. MaxNat

(* Inductive specification: any type‑correct state satisfying the invariant can be an initial state,
   and thereafter the system evolves according to Next while preserving the invariant. *)
ISpec == (TypeOK /\ Inv) /\ [] [Next]_vars

====