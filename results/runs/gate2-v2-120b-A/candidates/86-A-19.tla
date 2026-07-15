---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* ==========================================================================
\* Description:
\* This module defines backend pragmas for the TLA Proof System (TLAPS).
\* It provides operators that instruct the proof system to dispatch proof
\* obligations to various automated theorem provers and SMT solvers, and
\* includes fundamental proof rules for temporal logic reasoning.
\* ==========================================================================

\* -------------------------------------------------------------
\* Configuration constants (placeholders for backend pragma values)
\* -------------------------------------------------------------
CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4,
  ZenonTimeout, IsabelleTimeout, CVC3Timeout,
  YicesTimeout, veriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

\* -------------------------------------------------------------
\* Backend pragma operators (their bodies are uninterpreted; they
\* simply carry the configuration information to TLAPS)
\* -------------------------------------------------------------
ZenonBackend(t) == TRUE
IsabelleBackend(t) == TRUE
CVC3Backend(t) == TRUE
YicesBackend(t) == TRUE
VeriTBackend(t) == TRUE
Z3Backend(t) == TRUE
SPASSBackend(t) == TRUE
LS4Backend(t) == TRUE

\* -------------------------------------------------------------
\* Temporal logic proof rule placeholders
\* -------------------------------------------------------------
InvRule(Spec) == TRUE
WFRule(Spec) == TRUE
SFRule(Spec) == TRUE
StepSimRule(Spec) == TRUE

\* -------------------------------------------------------------
\* Specification (no concrete system state, only theorems)
\* -------------------------------------------------------------
Spec == ZenonBackend(ZenonTimeout) /\
        IsabelleBackend(IsabelleTimeout) /\
        CVC3Backend(CVC3Timeout) /\
        YicesBackend(YicesTimeout) /\
        VeriTBackend(veriTTimeout) /\
        Z3Backend(Z3Timeout) /\
        SPASSBackend(SPASSTimeout) /\
        LS4Backend(LS4Timeout) /\
        SetExtensionalityTheorem /\
        NoUniversalSetTheorem

\* -------------------------------------------------------------
\* Fundamental theorems
\* -------------------------------------------------------------
SetExtensionalityTheorem == \A x, y \in SUBSET Nat :
    (\A z \in Nat : (z \in x) = (z \in y)) => x = y

NoUniversalSetTheorem == \A x \in Nat : x \notin Nat

\* -------------------------------------------------------------
\* No concrete state variables; INIT and NEXT are trivially TRUE
\* -------------------------------------------------------------
Init == TRUE
Next == TRUE

\* -------------------------------------------------------------
\* SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES as required
\* -------------------------------------------------------------
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == SetExtensionalityTheorem
PROPERTIES == NoUniversalSetTheorem

====