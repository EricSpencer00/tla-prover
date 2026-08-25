---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------------
  Finite version of Nat for model checking.
  The configuration file will replace Nat with NatOverride, so all uses
  of Nat in the inherited Bakery specification become bounded by MaxNat.
-----------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------------
  Aliases required by the configuration.
-----------------------------------------------------------------------*)
INIT == Init
NEXT == Next

(*-----------------------------------------------------------------------
  Invariants required by the .cfg file.
  They are simply re‑exposed from the Bakery module.
-----------------------------------------------------------------------*)
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

(*-----------------------------------------------------------------------
  Inductive specification: start from any type‑correct state and require
  that every step respects the Next action.
-----------------------------------------------------------------------*)
ISpec == TypeOK /\ [][NEXT]_vars

(* No additional properties are needed for this configuration. *)
PROPERTIES == TRUE
====