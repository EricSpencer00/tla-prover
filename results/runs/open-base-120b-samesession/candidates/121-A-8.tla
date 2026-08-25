---- MODULE ZSequences ----
EXTENDS Naturals

(*\*  A finite version of Nat for model checking.  \*)
CONSTANT MaxChar

CharacterSet == 0 .. MaxChar - 1

====