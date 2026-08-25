---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend pragma placeholders for TLAPS
\* ----------------------------------------------------------------------
\* BEGIN ZENON
\* END ZENON

\* BEGIN ISABELLE
\* END ISABELLE

\* BEGIN CVC3
\* END CVC3

\* BEGIN YICES
\* END YICES

\* BEGIN VERIT
\* END VERIT

\* BEGIN Z3
\* END Z3

\* BEGIN SPASS
\* END SPASS

\* BEGIN LS4
\* END LS4

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule names (reserved)
\* ----------------------------------------------------------------------
THEOREM InvarianceRule == TRUE
THEOREM WellFormednessRule == TRUE
THEOREM StrongFairnessRule == TRUE
THEOREM WeakFairnessRule == TRUE
THEOREM StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* Specification skeleton (no concrete behavior)
\* ----------------------------------------------------------------------
VARIABLE dummy

Init == TRUE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====