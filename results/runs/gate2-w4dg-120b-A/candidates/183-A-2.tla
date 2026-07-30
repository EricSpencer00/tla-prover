---- MODULE TLAPS ----
EXTENDS Naturals

(* This module defines backend pragmas for the TLA Proof System (TLAPS). It     *)
(* provides operators that dispatch proof obligations to various automated     *)
(* provers (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4) and states    *)
(* fundamental proof rules for temporal logic reasoning, such as invariance,  *)
(* well-formedness, fairness, and step simulation.  It is a configuration       *)
(* module with no state.                                                       *)

CONSTANTS
    Zenon,
    Isabelle,
    CVC3,
    Yices,
    Verit,
    Z3,
    SPASS,
    LS4

(* Dispatch an obligation to the Zenon prover.  The arguments are the         *)
(* obligation name and the number of Zenon runs to attempt before giving up.   *)
ZenonF(o, n) == TRUE

(* Dispatch an obligation to the Isabelle prover.  The argument is the       *)
(* obligation name.                                                             *)
IsabelleF(o) == TRUE

(* Dispatch an obligation to the CVC3 prover.  The arguments are the          *)
(* obligation name and a per-run timeout.                                      *)
CVC3F(o, t) == TRUE

(* Dispatch an obligation to the Yices prover.  The argument is the           *)
(* obligation name.                                                             *)
YicesF(o) == TRUE

(* Dispatch an obligation to the veriT prover.  The argument is the           *)
(* obligation name.                                                             *)
VeritF(o) == TRUE

(* Dispatch an obligation to the Z3 prover.  The argument is the              *)
(* obligation name.                                                             *)
Z3F(o) == TRUE

(* Dispatch an obligation to the SPASS prover.  The argument is the           *)
(* obligation name.                                                             *)
SPASSF(o) == TRUE

(* Dispatch an obligation to the LS4 temporal logic prover.  The argument    *)
(* is the obligation name.                                                       *)
LS4F(o) == TRUE

(* Temporal logic proof rule: an invariance claim proved by simulation     *)
(* steps.  The argument is the action name the step simulates.                *)
SIMSTEP(a) == TRUE

(* Temporal logic proof rule: a well-formedness claim proved by a single     *)
(* step.                                                                        *)
WFSTEP(a) == TRUE

(* Temporal logic proof rule: strong fairness of an action                     *)
STRONGFAIR(a) == TRUE

(* Temporal logic proof rule: weak fairness of an action                       *)
WEAKFAIR(a) == TRUE

(* Set extensionality: two sets are equal if they contain the same elements.  *)
EXTENSIONALITY == TRUE

(* No set contains every possible value.                                        *)
NOSETCONTAINSALL == TRUE

\* No state, no actions: this is a pure configuration module.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {EXTENSIONALITY}
PROPERTIES == {NOSETCONTAINSALL}

====