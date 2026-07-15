---- MODULE TLAPS ----
EXTENDS Naturals, Reals, FiniteSets, Sequences

(***************************************************************************)
(*  TLAPS configuration primitives and temporal logic proof rule names.    *)
(*  No system state is modeled; the module only reserves the names of     *)
(*  operators that backends for the TLA+ Proof System (TLAPS) will      *)
(*  recognise.                                                             *)
(***************************************************************************)

(***************************************************************************)
(*  Operator names that identify various automated provers.                *)
(***************************************************************************)
Zenon(_)=TRUE
Isabelle(_)=TRUE
CVC3(_)=TRUE
Yices(_)=TRUE
VeriT(_)=TRUE
Z3(_)=TRUE
SPASS(_)=TRUE
LS4(_)=TRUE

(***************************************************************************)
(*  Temporal logic proof rule names.                                       *)
(***************************************************************************)
InvRule(_,_)=TRUE          \* invariance rule
WFair(_)=TRUE              \* weak fairness rule
SFair(_)=TRUE              \* strong fairness rule
StepSim(_,_)=TRUE          \* step simulation rule

(***************************************************************************)
(*  Fundamental theorems (set extensionality and universe non‑collapse).   *)
(***************************************************************************)
SetExtensionality == 
  \A A, B \in SUBSET UNIV : (\A x : x \in A <=> x \in B) => A = B

NoUniverseCollapse == 
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

(***************************************************************************)
(*  Specification scaffolding – required identifiers for a TLC config.    *)
(*  The module does not describe any concrete state, so the operators are *)
(*  defined to hold trivially.                                            *)
(***************************************************************************)

VARIABLE dummy

Init == dummy \in {0}
Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INIT == Init
NEXT == Next

INVARIANTS == {}
PROPERTIES == {}

=============================================================================