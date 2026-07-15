---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(*  Backend pragma definitions for TLAPS                                   *)
(*  These operators are placeholders that TLAPS interprets as directives   *)
(*  to invoke specific provers.  They have no operational effect on the   *)
(*  model itself.                                                          *)
(***************************************************************************)

Zeno(pr) == TRUE
Isabelle(pr) == TRUE
CVC3(pr) == TRUE
Yices(pr) == TRUE
Verit(pr) == TRUE
Z3(pr) == TRUE
Spass(pr) == TRUE
LS4(pr) == TRUE

(***************************************************************************)
(*  Temporal logic proof rule names (placeholders)                         *)
(***************************************************************************)

InvRule == TRUE
WfRule == TRUE
SfRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE

(***************************************************************************)
(*  Set extensionality theorem (as a theorem)                             *)
(***************************************************************************)

Extensionality == \A A, B \in SUBSET UNIV : (\A x \in UNIV : x \in A <=> x \in B) => A = B

(***************************************************************************)
(*  "No set contains every possible value" theorem                         *)
(***************************************************************************)

NoUniversalSet == \A S \in SUBSET UNIV : S # UNIV

=============================================================================