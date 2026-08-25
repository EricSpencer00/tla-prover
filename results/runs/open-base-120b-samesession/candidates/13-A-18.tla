---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(* Finite replacement for the infinite set Nat *)
NatOverride == 0 .. MaxNat

(* Inductive specification: any state satisfying the type invariant and the full
   inductive invariant may be the start, and all behaviours must follow Next. *)
ISpec == TypeOK /\ Inv /\ [][Next]_(<<pc, ticket, choosing>>)

====