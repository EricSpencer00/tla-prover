---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*************************************************************************)
(* Backends (pragmas) for TLAPS                                            *)
(* These pragmas are placeholders to indicate which provers should be   *)
(* used. They are defined as nullary operators so they can be referenced *)
(* in the .cfg file without affecting the semantics of the model.        *)
(*************************************************************************)

Zenon      == TRUE
Isabelle   == TRUE
CVC3       == TRUE
Yices      == TRUE
VeriT      == TRUE
Z3         == TRUE
SPASS      == TRUE
LS4        == TRUE

(*************************************************************************)
(* Timeouts and tactics (also placeholders)                              *)
(*************************************************************************)

ZenonTimeout      == 5
CVC3Timeout       == 10
YicesTimeout      == 10
VeriTTimeout      == 10
Z3Timeout         == 10
SPASSTimeout      == 10
LS4Timeout        == 10

(*************************************************************************)
(* Temporal logic proof rules (names reserved for future use)            *)
(*************************************************************************)

InvRule      == TRUE
WFRule       == TRUE
SFRule       == TRUE
StepSim      == TRUE
StrongFairness == TRUE
WeakFairness   == TRUE

(*************************************************************************)
(* Fundamental theorems (safety properties)                              *)
(*************************************************************************)

SetExtensionality ==
  \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B

NoSetContainsAll ==
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

(*************************************************************************)
(* State variables (no concrete state needed)                             *)
(*************************************************************************)

VARIABLES dummy

(*************************************************************************)
(* Initial state                                                          *)
(*************************************************************************)

Init ==
  dummy = 0

(*************************************************************************)
(* Next-state relation (trivial, does nothing)                           *)
(*************************************************************************)

Next ==
  UNCHANGED dummy

(*************************************************************************)
(* Specification (standard TLA+ idiom)                                    *)
(*************************************************************************)

Spec ==
  Init /\ [][Next]_<<dummy>>

(*************************************************************************)
(* Theorems exported by the module                                         *)
(*************************************************************************)

THEOREM SetExtTheorem == SetExtensionality
THEOREM NoAllTheorem   == NoSetContainsAll

=============================================================================