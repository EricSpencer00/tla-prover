---- MODULE TLAPS ----
\* This module provides backend configuration placeholders for TLAPS and
\* includes fundamental set-theoretic theorems and the required
\* specification operators.

(*---------------------------------------------------------------------*)
(*  Specification skeleton                                            *)
(*---------------------------------------------------------------------*)

Init == TRUE
Next == UNCHANGED <<>>

SPECIFICATION == Init /\ [][Next]_<<>>

INVARIANTS == {}
PROPERTIES == {}

(*---------------------------------------------------------------------*)
(*  Fundamental theorems                                             *)
(*---------------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====