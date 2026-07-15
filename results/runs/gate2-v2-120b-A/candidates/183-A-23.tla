---- MODULE TLAPS ----
EXTENDS Naturals, Reals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Backend pragmas for the TLA Proof System (TLAPS).                      *)
(*  This module declares operators that instruct TLAPS to use various     *)
(*  automated provers and solvers, and it states two fundamental theore-   *)
(*  retical lemmas that are always true.                                   *)
(*                                                                       *)
(*  No state variables, actions, safety or liveness properties are      *)
(*  specified here; this module serves purely as a configuration and      *)
(*  lemma library.                                                        *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Backend provers configuration
\* ----------------------------------------------------------------------
\* The following operators are no-ops at the level of the model.  They are
\* intended to be recognized by the TLAPS toolchain as directives.
\* The definitions are deliberately simple: each returns the argument
\* unchanged, thereby having no effect on the model's behaviour.
\* ----------------------------------------------------------------------
Zenon(expr)          == expr
Isabelle(expr)       == expr
CVC3(expr)           == expr
Yices(expr)          == expr
VeriT(expr)          == expr
Z3(expr)             == expr
SPASS(expr)          == expr
LS4(expr)            == expr

ZenonAuto(expr)      == Zenon(expr)
IsabelleAuto(expr)   == Isabelle(expr)
CVC3Auto(expr)       == CVC3(expr)
YicesAuto(expr)      == Yices(expr)
VeriTAuto(expr)      == VeriT(expr)
Z3Auto(expr)         == Z3(expr)
SPASSAuto(expr)      == SPASS(expr)
LS4Auto(expr)        == LS4(expr)

\* ----------------------------------------------------------------------
\* Fundamental set-theoretic lemmas
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A X, Y \in SUBSET UNIV :
    (\A z : z \in X <=> z \in Y) => X = Y

NoSetContainsAll ==
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

\* ----------------------------------------------------------------------
\* Specification stubs (required by the .cfg, though they are not used)
\* ----------------------------------------------------------------------
VARIABLES dummy

Init ==
  dummy = 0

Next ==
  dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\* The spec, init, next, invariants, and properties that the .cfg expects
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANTS    == {}
PROPERTIES    == {}

=============================================================================