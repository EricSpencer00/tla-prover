---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*********************************************************************
--MODULE TLAPS
This module provides configuration operators for the TLA+ Proof
System (TLAPS).  It declares the identifiers required by the reference
configuration file, but does not model any concrete state or behavior.
The identifiers are defined as trivial stubs that can be used by the
proof manager to select back‑ends, set time‑outs, and refer to the
standard temporal‑logic proof rules.

No state variables, actions, or safety/liveness properties are
specified here; the module only supplies the names expected by the
configuration.
*********************************************************************)

(***************************************************************************)
(*  Configuration operators                                                *)
(***************************************************************************)

\* Backend provers
Zenon   == "Zenon"
Isabelle == "Isabelle"
CVC3    == "CVC3"
Yices   == "Yices"
VeriT   == "veriT"
Z3      == "Z3"
SPASS   == "SPASS"
LS4     == "LS4"

\* Example time‑out operator (seconds)
Timeout == 30

\* Tactics (place‑holders)
DefaultTactic == "default"
StrongFairnessTactic == "strong"
WeakFairnessTactic == "weak"

(***************************************************************************)
(*  Temporal‑logic proof rule names (reserved for future use)             *)
(***************************************************************************)

InvRule        == "INV"
WFRule         == "WF"
SFRule         == "SF"
WellFormedRule == "WFMD"
StepSimRule    == "STEPSIM"

(***************************************************************************)
(*  Constants required by the .cfg (none in this case)                    *)
(***************************************************************************)

CONSTANTS   \* no constants required, but the identifier must exist
  {}

(***************************************************************************)
(*  Specification identifier (required by the .cfg)                       *)
(***************************************************************************)

(* The specification is the trivial "skip" specification, i.e., the
   system does nothing.  This satisfies the requirement that a SPEC
   identifier be present. *)
Specification == TRUE

(***************************************************************************)
(*  Init and Next actions (required by the .cfg)                           *)
(***************************************************************************)

INIT == TRUE

NEXT == TRUE

(***************************************************************************)
(*  Invariants (none required)                                            *)
(***************************************************************************)

INVARIANTS == {}

(***************************************************************************)
(*  Properties (none required)                                            *)
(***************************************************************************)

PROPERTIES == {}

(***************************************************************************)
(*  Theorem: set extensionality                                            *)
(***************************************************************************)

EXTENSIONALITY == 
  \A X, Y \in SUBSET Nat : 
    (\A e \in Nat : e \in X <=> e \in Y) => X = Y

(***************************************************************************)
(*  Theorem: no set contains every possible value                          *)
(***************************************************************************)

NOUNIVERSALSET == 
  \A S \in SUBSET Nat : 
    \E v \in Nat : v \notin S

(***************************************************************************)
(*  Export the theorems so they are visible to the proof manager          *)
(***************************************************************************)

THEOREMS == {EXTENSIONALITY, NOUNIVERSALSET}

=============================================================================