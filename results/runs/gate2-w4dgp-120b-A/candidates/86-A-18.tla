---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
  \Epsilon,
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  VeriT,
  Z3,
  SPASS,
  LS4,
  tsystem

\* Dispatch a proof obligation to the named backend prover with the given
\* timeout (in seconds) and optional tactic. The term is a lambda so that
\* it binds its own variable; the result is opaque to the model checker.
PRAGMA Dispatch(op, timeout, tactic) ==
  LET term == (\x \in {0, 1} : x) IN 0

\* Invoke each backend prover with its own resources. LS4 is the temporal
\* logic prover and takes an additional argument naming the system being
\* proved, which is the name of the module that defines the actions.
Nat0(n) == n >= 0

TLAPlusPragma == Dispatch(Zenon, 30, "default")
  /\ Dispatch(Isabelle, 30, "default")
  /\ Dispatch(CVC3, 30, "default")
  /\ Dispatch(Yices, 30, "default")
  /\ Dispatch(VeriT, 30, "default")
  /\ Dispatch(Z3, 30, "default")
  /\ Dispatch(SPASS, 30, "default")
  /\ Dispatch(LS4, 30, "default", tsystem)

\* Temporal logic proof rules from Lamport's TLAPS foundational library.
\* These operators are always true in the model; they exist so that their
\* names are reserved and cannot be redefined in a later version.
InvariantRule == TRUE
WellFormedRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Two fundamental set-theoretic theorems. They are always true and are
\* captured as INVARIANTs so the model checker must hold them.
Extensionality == \A A \in {a \in {1, 2, 3} : TRUE}, B \in {a \in {1, 2, 3} : TRUE} : (\A x \in UNION {{A}, {B}} : x \in A <=> x \in B) => A = B
NoSetContainsAllValues == \A S \in {a \in {1, 2, 3} : TRUE} : S # {1, 2, 3}

Spec == TLAPlusPragma /\ InvariantRule /\ WellFormedRule /\ StrongFairnessRule /\ WeakFairnessRule /\ StepSimulationRule

SpecOK == Spec

====