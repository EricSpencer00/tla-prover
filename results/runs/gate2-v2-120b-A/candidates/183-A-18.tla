---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Backend pragmas for the TLA Proof System (TLAPS).  These operators
  are placeholders that TLAPS recognises as instructions to invoke
  specific automated theorem provers or SMT solvers.  The module
  does not model any concrete system behaviour; its purpose is to
  provide the symbolic names used by the proof manager.
-----------------------------------------------------------------*)

\* -----------------------------------------------------------------
\* Backend provers and solvers
\* -----------------------------------------------------------------
Zenon     == TRUE
Isabelle  == TRUE
CVC3      == TRUE
Yices     == TRUE
VeriT     == TRUE
Z3        == TRUE
SPASS     == TRUE
LS4       == TRUE

\* -----------------------------------------------------------------
\* Temporal proof rules (names only; they are no-ops in the model)
\* -----------------------------------------------------------------
InvRule   == TRUE   \* Invariance rule
WFRule    == TRUE   \* Weak fairness rule
SFRule    == TRUE   \* Strong fairness rule
StepSim   == TRUE   \* Step simulation rule

\* -----------------------------------------------------------------
\* Fundamental theorems (expressed as theorems in the module)
\* -----------------------------------------------------------------
SetExtensionality ==
    \A X, Y \in SUBSET UNIV : (\A z : (z \in X) <=> (z \in Y)) => X = Y

NoSetContainsAll ==
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* -----------------------------------------------------------------
\* Operators required by the .cfg (names only, no concrete semantics)
\* -----------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == TRUE
PROPERTIES    == TRUE

=============================================================================