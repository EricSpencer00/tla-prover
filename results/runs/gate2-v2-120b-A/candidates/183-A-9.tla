---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  TLAPS: Configuration infrastructure for the TLA Proof System (TLAPS).   *)
(*  This module declares the backend provers, timeouts, tactics, and the   *)
(*  fundamental temporal logic proof rules.  It also provides two basic    *)
(*  theorems: set extensionality and the impossibility of a universal set. *)
(***************************************************************************)

\* ------------------------------------------------------------------------
\*  Backend prover configuration (constants)
\* ------------------------------------------------------------------------
CONSTANTS
    ZenonTimeout,    \* timeout in seconds for Zenon
    IsabelleTimeout, \* timeout in seconds for Isabelle
    CVC3Timeout,      \* timeout in seconds for CVC3
    YicesTimeout,    \* timeout in seconds for Yices
    veriTTimeout,    \* timeout in seconds for veriT
    Z3Timeout,       \* timeout in seconds for Z3
    SPASSTimeout,    \* timeout in seconds for SPASS
    LS4Timeout,      \* timeout in seconds for LS4
    ZenonTactic,     \* optional tactic string for Zenon
    IsabelleTactic,  \* optional tactic string for Isabelle
    CVC3Tactic,      \* optional tactic string for CVC3
    YicesTactic,     \* optional tactic string for Yices
    veriTTactic,     \* optional tactic string for veriT
    Z3Tactic,        \* optional tactic string for Z3
    SPASSTactic,     \* optional tactic string for SPASS
    LS4Tactic,       \* optional tactic string for LS4
    Theory,          \* optional additional theory for SMT solvers
    Provers          \* the set of provers to be used

\* ------------------------------------------------------------------------
\*  Proof rule names (no functional content; they are reserved identifiers)
\* ------------------------------------------------------------------------
PROOF_RULES ==
    {"InvRule", "WFRule", "SFRule", "Induction", "StepSimulation"}

\* ------------------------------------------------------------------------
\*  No state variables: the module does not model a concrete system.
\* ------------------------------------------------------------------------
VARIABLES

\* ------------------------------------------------------------------------
\*  The specification is trivial: everything is allowed.
\* ------------------------------------------------------------------------
Spec == TRUE

Init == TRUE
Next == TRUE

\* The specification required by the `SPECIFICATION` identifier.
SPECIFICATION == Spec

\* ------------------------------------------------------------------------
\*  Safety theorems
\* ------------------------------------------------------------------------
SetExtensionality ==
    \A A, B \in SUBSET UNIV : (\A x : x \in A <=> x \in B) => A = B

NoUniversalSet ==
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* ------------------------------------------------------------------------
\*  The identifiers required by the (empty) .cfg file
\* ------------------------------------------------------------------------
INVARIANTS == {}
PROPERTIES == {}
INIT == Init
NEXT == Next

=============================================================================