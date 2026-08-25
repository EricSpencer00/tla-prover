---- MODULE ZSequences ----
EXTENDS Naturals

\* Finite character set used to replace Nat in the main specification.
\* This definition provides a concrete, checkable set of characters.
CharacterSet == 0..9
====