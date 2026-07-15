---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  Backend pragma operators for various automated theorem provers and SMT   *)
(*  solvers.  These operators are no-ops at the level of the TLA+ model;   *)
(*  they exist solely so that the proof manager can recognize the         *)
(*  names and dispatch proof obligations accordingly.                     *)
(***************************************************************************)

\* Provers that may be invoked by TLAPS
Zenon   == "Zenon"
Isabelle == "Isabelle"
CVC3    == "CVC3"
Yices   == "Yices"
VeriT   == "VeriT"
Z3      == "Z3"
SPASS   == "SPASS"
LS4     == "LS4"

\* Backend pragma operators (no effect on the model)
Zenon(proof)      == proof
Isabelle(proof)   == proof
CVC3(proof)       == proof
Yices(proof)      == proof
VeriT(proof)      == proof
Z3(proof)         == proof
SPASS(proof)      == proof
LS4(proof)        == proof

(***************************************************************************)
(*  Temporal‑logic proof rules (names only; no implementation)            *)
(***************************************************************************)

InvRule == TRUE          \* invariance rule placeholder
WFRule  == TRUE          \* weak‑fairness rule placeholder
SFRule  == TRUE          \* strong‑fairness rule placeholder
StepSim == TRUE          \* step‑simulation rule placeholder

(***************************************************************************)
(*  Fundamental set‑theoretic theorems (expressed as theorems)            *)
(***************************************************************************)

SetExtensionality == 
  \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet == 
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

(***************************************************************************)
(*  Required identifiers from the (empty) .cfg file                        *)
(***************************************************************************)

(* There are no state variables, actions, or safety/liveness properties   *)
(* to be defined because the description specifies that the module serves *)
(* only as a configuration/infrastructure module.                         *)

(***************************************************************************)
(*  The SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES operators   *)
(*  must exist even if they are trivial placeholders.                     *)
(***************************************************************************)

Init == TRUE
Next == TRUE

Spec == Init /\ [][Next]_<<>>

INVARIANTS == {}
PROPERTIES == {}

(***************************************************************************)
(*  The module does not expose any additional symbols beyond those        *)
(*  required above.                                                        *)
(***************************************************************************)

====