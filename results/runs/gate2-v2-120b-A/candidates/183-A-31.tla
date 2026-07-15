---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Constants (none needed for the description)                             *)
(***************************************************************************)

(***************************************************************************)
(* State variables (none specified)                                         *)
(***************************************************************************)

(***************************************************************************)
(* Operators required by the config                                         *)
(***************************************************************************)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == [][TRUE]_<<>>
INVARIANTS == SetExtensionality /\ NoSetContainsAll
PROPERTIES == SetExtensionality /\ NoSetContainsAll

(***************************************************************************)
(* Fundamental theorems (theorems are defined as operators that are TRUE   *)
(* if their logical statement holds). In a real setting they would be     *)
(* proved, but for a specification we simply assert the statements.      *)
(***************************************************************************)

SetExtensionality == 
  \A S, T \in SUBSET UNIV :
    (\A x : x \in S <=> x \in T) => S = T

NoSetContainsAll == 
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

=============================================================================