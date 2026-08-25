---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

\* -----------------------------------------------------------------
\* Backend pragmas for the TLAPS proof manager
\* -----------------------------------------------------------------
\* @backend Zenon
\* @backend Isabelle
\* @backend CVC3
\* @backend Yices
\* @backend veriT
\* @backend Z3
\* @backend SPASS
\* @backend LS4

\* -----------------------------------------------------------------
\* Temporal‑logic proof‑rule names (place‑holders only)
\* -----------------------------------------------------------------
InvarianceRule      == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule   == TRUE
StepSimulationRule == TRUE

\* -----------------------------------------------------------------
\* Fundamental set‑theoretic theorems
\* -----------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

\* -----------------------------------------------------------------
\* Specification skeleton (required identifiers)
\* -----------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<>>
INIT          == Init
NEXT          == Next
INVARIANTS    == << >>
PROPERTIES    == << >>

\* -----------------------------------------------------------------
\* Trivial state (no state variables are described)
\* -----------------------------------------------------------------
Init == TRUE
Next == TRUE

====