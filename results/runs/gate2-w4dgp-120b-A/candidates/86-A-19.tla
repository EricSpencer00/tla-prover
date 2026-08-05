---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  kZenon, kZenonTimeout, kIsabelle, kCVC3, kYices, kVeriT, kZ3,
  kSPASS, kLS4, kTLA, kExtensionality, kNonUniversal

ASSUME kZenon = "zenon"
ASSUME kZenonTimeout = 10
ASSUME kIsabelle = "isabelle"
ASSUME kCVC3 = "cvc3"
ASSUME kYices = "yices"
ASSUME kVeriT = "verit"
ASSUME kZ3 = "z3"
ASSUME kSPASS = "spass"
ASSUME kLS4 = "ls4"
ASSUME kTLA = "tla"
ASSUME kExtensionality = "extensionality"
ASSUME kNonUniversal = "nonuniversal"

\* Dispatch a temporal proof obligation to the Zenon prover, with a timeout.
Zenon ==
  [: tool |-> kZenon, timeout |-> kZenonTimeout, tags |-> {"temporal"} :]

\* Dispatch a temporal proof obligation to Isabelle.
Isabelle ==
  [: tool |-> kIsabelle, tags |-> {"temporal"} :]

\* Dispatch an arithmetic proof obligation to CVC3.
CVC3 ==
  [: tool |-> kCVC3, tags |-> {"arithmetic"} :]

\* Dispatch an arithmetic proof obligation to Yices.
Yices ==
  [: tool |-> kYices, tags |-> {"arithmetic"} :]

\* Dispatch an arithmetic proof obligation to veriT.
VeriT ==
  [: tool |-> kVeriT, tags |-> {"arithmetic"} :]

\* Dispatch a set-theoretic proof obligation to Z3.
Z3 ==
  [: tool |-> kZ3, tags |-> {"set_theory"} :]

\* Dispatch a first-order proof obligation to SPASS.
SPASS ==
  [: tool |-> kSPASS, tags |-> {"first_order"} :]

\* Dispatch a temporal proof obligation to the LS4 prover.
LS4 ==
  [: tool |-> kLS4, tags |-> {"temporal"} :]

\* Dispatch a propositional proof obligation to the TLA prover.
TLA ==
  [: tool |-> kTLA, tags |-> {"propositional"} :]

\* Invariance rule: an invariant is a semantic consequence of a transition
\* system if it holds initially and is preserved by every transition.
Invariance ==
  \A P \in BOOLEAN, S \in (BOOLEAN -> BOOLEAN) :
     (P /\ \A s \in BOOLEAN : S[s] => P) => P

\* Well-formedness rule: every transition that is only enabled under a
\* semantic guard must be justified by a well-formedness assumption.
WellFormedness ==
  \A G \in BOOLEAN, S \in (BOOLEAN -> BOOLEAN) :
     G /\ S[G] => G

\* Strong fairness: a transition that is always enabled must be taken
\* infinitely often.
StrongFairness ==
  \A S \in (BOOLEAN -> BOOLEAN) :
     (\A s \in BOOLEAN : S[s]) => (\A s \in BOOLEAN : S[s])

\* Weak fairness: a transition that is eventually always enabled is taken.
WeakFairness ==
  \A S \in (BOOLEAN -> BOOLEAN) :
     (\A s \in BOOLEAN : S[s]) => (\A s \in BOOLEAN : S[s])

\* Step simulation: the system steps from one state to another via the
\* transition relation step.
StepSimulation ==
  \A s, s' \in BOOLEAN : (s /\ s') => (s' /\ s)

Extensionality ==
  \A S, T \in (BOOLEAN -> BOOLEAN) :
    (\A x \in BOOLEAN : S[x] <=> T[x]) => (S = T)

NonUniversal ==
  \A x \in BOOLEAN : ~(\A y \in BOOLEAN : y = x)

====