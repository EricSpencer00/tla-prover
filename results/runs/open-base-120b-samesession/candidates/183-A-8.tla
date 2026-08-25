---- MODULE TLAPS ----
EXTENDS FiniteSets, Sequences, TLC

\* --------------------------------------------------------------
\* Backend configuration operators for TLAPS
\* --------------------------------------------------------------

Zenon(proof, timeout) == [backend |-> "Zenon", proof |-> proof,
                         timeout |-> timeout]

Isabelle(proof, timeout) == [backend |-> "Isabelle", proof |-> proof,
                             timeout |-> timeout]

CVC3(proof, timeout) == [backend |-> "CVC3", proof |-> proof,
                         timeout |-> timeout]

Yices(proof, timeout) == [backend |-> "Yices", proof |-> proof,
                          timeout |-> timeout]

VeriT(proof, timeout) == [backend |-> "veriT", proof |-> proof,
                          timeout |-> timeout]

Z3(proof, timeout) == [backend |-> "Z3", proof |-> proof,
                       timeout |-> timeout]

SPASS(proof, timeout) == [backend |-> "SPASS", proof |-> proof,
                          timeout |-> timeout]

LS4(proof, timeout) == [backend |-> "LS4", proof |-> proof,
                        timeout |-> timeout]

\* --------------------------------------------------------------
\* Fundamental set-theoretic theorems
\* --------------------------------------------------------------

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  ~\E S \in SUBSET UNIV : \A x \in UNIV : x \in S

\* --------------------------------------------------------------
\* Temporal‑logic proof rules (place‑holders)
\* --------------------------------------------------------------

\* Invariance rule: from an invariant I and a step relation, infer that I holds always.
InvarianceRule(I, Next) == TRUE

\* Well‑formedness rule: ensures actions are well‑formed w.r.t. the state.
WellFormednessRule(Action) == TRUE

\* Strong fairness rule.
StrongFairnessRule(Action) == TRUE

\* Weak fairness rule.
WeakFairnessRule(Action) == TRUE

\* Step simulation rule.
StepSimulationRule(SrcStep, TgtStep) == TRUE

====