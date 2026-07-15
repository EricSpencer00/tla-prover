---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  TLAPS: Configuration infrastructure for the TLA Proof System (TLAPS).  *)
(*  This module defines operators that select backend provers and declares  *)
(*  fundamental temporal logic proof rules and theorems required for later *)
(*  specifications.  No state variables or actions are modeled here.      *)
(***************************************************************************)

(***************************************************************************)
(*  Backend prover configuration operators                                *)
(***************************************************************************)

(* Time-out (in seconds) for each prover.  Adjust as needed by the user. *)
ZenonTimeout  == 5
IsabelleTimeout == 5
CVC3Timeout   == 5
YicesTimeout  == 5
VeritTimeout  == 5
Z3Timeout     == 5
SPASSTimeout  == 5
LS4Timeout    == 5

(* Backend prover selectors.  Each operator returns a string identifying   *)
(* the prover to be used for a given proof obligation.                     *)
Zenon   == "zenon"
Isabelle == "isabelle"
CVC3    == "cvc3"
Yices   == "yices"
Verit   == "verit"
Z3      == "z3"
SPASS   == "spass"
LS4     == "ls4"

(***************************************************************************)
(*  Temporal logic proof rules (place‑holders, no operational semantics)   *)
(***************************************************************************)

(* Invariance rule: if Init => Inv and Inv /\ [Next]_vars => Inv, then Inv holds forever. *)
InvariantRule == TRUE

(* Well‑formedness rule for temporal formulas. *)
WFRule == TRUE

(* Strong fairness rule. *)
StrongFairness == TRUE

(* Weak fairness rule. *)
WeakFairness == TRUE

(* Step‑simulation rule (used to relate concrete and abstract steps). *)
StepSimulation == TRUE

(***************************************************************************)
(*  Fundamental theorems                                                   *)
(***************************************************************************)

(* Set extensionality: two sets are equal iff they have the same elements. *)
SetExtensionality ==
  \A A, B : (A = B) <=> (\A x : x \in A <=> x \in B)

(* No set contains every possible value (universe is not a member of itself). *)
NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

(***************************************************************************)
(*  Specification skeleton (no concrete state)                            *)
(***************************************************************************)

(* No state variables are declared; the following operators are defined   *)
(* merely to satisfy the expected identifiers from the .cfg file.          *)

SPECIFICATION == Init /\ [] [][Next]_vars

Init == TRUE

Next == UNCHANGED vars

(* The set of all variables, required by the sugar [_] in the Next action. *)
vars == {}

INVARIANTS == SetExtensionality

PROPERTIES == NoUniversalSet

=============================================================================