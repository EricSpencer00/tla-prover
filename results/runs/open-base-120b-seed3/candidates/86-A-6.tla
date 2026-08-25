---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*-------------------------------------------------------------------*)
(*  Backend pragma placeholders (no actual pragmas needed)         *)
(*-------------------------------------------------------------------*)

(*-------------------------------------------------------------------*)
(*  Trivial state (no variables)                                    *)
(*-------------------------------------------------------------------*)

Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [] [Next]_<<>>

INVARIANTS == {}

PROPERTIES == {}

(*-------------------------------------------------------------------*)
(*  Fundamental theorems                                            *)
(*-------------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    ( \A x : (x \in S) <=> (x \in T) ) => S = T

THEOREM NoUniversalSet ==
  \A S : ~ ( \A x : x \in S )

=============================================================================