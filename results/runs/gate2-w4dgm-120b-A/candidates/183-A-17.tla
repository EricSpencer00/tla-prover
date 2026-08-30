---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS ProofObligation, Timeout, MaxStep

\* Backend pragmas: each operators dispatches a proof obligation to a specific
\* prover/SMT solver or invokes a named proof rule.
\* All identifiers below (including the rule names from Lamport's TLA+ paper)
\* are deliberately present and reserved so they cannot be silently dropped or
\* renamed and cause a clash with a later module importing this one.

DispatchZenon == [kind |-> "dispatch", prover |-> "zenon"]
DispatchIsabelle == [kind |-> "dispatch", prover |-> "isabelle"]
DispatchCVC3 == [kind |-> "dispatch", prover |-> "cvc3"]
DispatchYices == [kind |-> "dispatch", prover |-> "yices"]
DispatchVeriT == [kind |-> "dispatch", prover |-> "verit"]
DispatchZ3 == [kind |-> "dispatch", prover |-> "z3"]
DispatchSPASS == [kind |-> "dispatch", prover |-> "spass"]
DispatchLS4 == [kind |-> "dispatch", prover |-> "ls4"]
DispatchTLA == [kind |-> "dispatch", prover |-> "tla"]

RuleInv == [kind |-> "rule", name |-> "invariance"]
RuleWf == [kind |-> "rule", name |-> "wellformed"]
RuleSF == [kind |-> "rule", name |-> "strongfair"]
RuleWF == [kind |-> "rule", name |-> "weakfair"]
RuleSim == [kind |-> "rule", name |-> "simulation"]

Pragmas == {
  DispatchZenon, DispatchIsabelle, DispatchCVC3, DispatchYices,
  DispatchVeriT, DispatchZ3, DispatchSPASS, DispatchLS4, DispatchTLA,
  RuleInv, RuleWf, RuleSF, RuleWF, RuleSim
}

\* Each proof obligation starts with no backend chosen and a fresh step budget.
InitObs(o) == [o |-> o, kind |-> "pending", budget |-> MaxStep]

\* SAFETY PROPERTY: the set of chosen backends is always a subset of the
\* declared pragmas, and the step budget never drops below zero.
Spec == \E o \in ProofObligation : InitObs(o)
Next == \E o \in ProofObligation, pc \in Pragmas :
  /\ pc.kind = "dispatch"
  /\ Spec' = [Spec EXCEPT ![o] = [o |-> o, kind |-> pc.prover, budget |-> @.budget]]
  /\ Spec[m \in ProofObligation |-> IF m = o THEN [o |-> m, kind |-> pc.prover, budget |-> @.budget] ELSE @]

BudgetBound == \A o \in ProofObligation : Spec[o].budget >= 0

\* LIVENESS PROPERTY: every proof obligation eventually gets dispatched to a
\* backend prover, rather than remaining pending forever.
EventualDispatch == \A o \in ProofObligation : (Spec[o].kind = "pending") ~> (Spec[o].kind # "pending")

\* FOUNDEDATIONAL THEOREMS: set extensionality and the existence of a value outside any given set.
SetExtensionality ==
  \A A, B \in SUBSET ProofObligation :
    (\A x \in ProofObligation : (x \in A) <=> (x \in B)) => (A = B)

NonUniversalSet ==
  \A A \in SUBSET ProofObligation :
    (\E x \in ProofObligation : x \notin A)

SPECIFICATION == Spec
INIT == Spec
NEXT == Next
INVARIANTS == BudgetBound
PROPERTIES == NonUniversalSet
====