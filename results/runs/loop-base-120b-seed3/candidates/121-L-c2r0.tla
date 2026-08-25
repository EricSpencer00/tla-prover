---- MODULE ZSequences ----
EXTENDS Naturals

CONSTANT MaxChar

(* A finite version of Nat used to bound indices for model checking. *)
CharacterSet == 0 .. (MaxChar - 1)

ASSUME MaxChar \in Nat \ {0}
====