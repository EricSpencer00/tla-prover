---- MODULE LeastCircularSubstring -------------------------------------------------
(***************************************************************************)
(* An implementation of the lexicographically-least circular substring     *)
(* algorithm from the 1980 paper by Kellogg S. Booth. See:                 *)
(* https://doi.org/10.1016/2.0190(80)90149-0                            *)
(***************************************************************************)

EXTENDS Integers, ZSequences

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

(****************************************************************************
                  The algorithm (Pseudocode)
=============================================================================