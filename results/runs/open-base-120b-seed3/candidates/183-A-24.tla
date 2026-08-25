---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Backend provers used by TLAPS.  The definitions are trivial; the
\* real effect is the TLAPS pragma attached to each operator.
\* ----------------------------------------------------------------------
\* TLAPS pragma: ZENON
Zenon(p) == p

\* TLAPS pragma: ISABELLE
Isabelle(p) == p

\* TLAPS pragma: CVC3
Cvc3(p) == p

\* TLAPS pragma: YICES
Yices(p) == p

\* TLAPS pragma: VERIT
VeriT(p) == p

\* TLAPS pragma: Z3
Z3(p) == p

\* TLAPS pragma: SPASS
Spass(p) == p

\* TLAPS pragma: LS4
Ls4(p) == p

\* ----------------------------------------------------------------------
\* Fundamental set-theoretic theorems.
\* ----------------------------------------------------------------------
\* Set extensionality: two sets are equal iff they have the same elements.
THEOREM SetExtensionality ==
  \A S, T : (S = T) \equiv (\A x : (x \in S) \equiv (x \in T))

\* There is no universal set that contains every possible value.
THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names are reserved for future use).
\* The bodies are left as trivial definitions; the real meaning is
\* provided by the TLAPS proof system.
\* ----------------------------------------------------------------------
\* Invariance rule
InvariantRule(p) == p

\* Well‑formedness rule
WellFormedRule(p) == p

\* Strong fairness rule
StrongFairnessRule(p) == p

\* Weak fairness rule
WeakFairnessRule(p) == p

\* Step simulation rule
StepSimulationRule(p) == p

====