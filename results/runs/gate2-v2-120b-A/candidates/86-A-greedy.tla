---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators for TLAPS
\* ----------------------------------------------------------------------
\* Each operator returns a string that TLAPS interprets as a directive.
\* The arguments are kept generic; the implementation does not use them.
\* ----------------------------------------------------------------------
Zenon(timeout) == "ZENON " \o timeout
Isabelle(timeout) == "ISABELLE " \o timeout
CVC3(timeout) == "CVC3 " \o timeout
Yices(timeout) == "YICES " \o timeout
VeriT(timeout) == "VERIT " \o timeout
Z3(timeout) == "Z3 " \o timeout
SPASS(timeout) == "SPASS " \o timeout
LS4(timeout) == "LS4 " \o timeout

\* ----------------------------------------------------------------------
\* Temporal logic proof rule names (reserved, no implementation)
\* ----------------------------------------------------------------------
InvarianceRule == "InvarianceRule"
WellFormednessRule == "WellFormednessRule"
StrongFairnessRule == "StrongFairnessRule"
WeakFairnessRule == "WeakFairnessRule"
StepSimulationRule == "StepSimulationRule"

\* ----------------------------------------------------------------------
\* State variable (the only one needed for the trivial model)
\* ----------------------------------------------------------------------
VARIABLE x

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init == x = 0

\* ----------------------------------------------------------------------
\* Next-state relation (does nothing but allows stuttering)
\* ----------------------------------------------------------------------
Next == UNCHANGED x

\* ----------------------------------------------------------------------
\* Specification (temporal formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Safety theorems derived from the description
\* ----------------------------------------------------------------------
SetExtensionality == 
  \A A, B \in SUBSET UNIV : (\A y : y \in A <=> y \in B) => A = B

NoUniversalSet == 
  \A S \in SUBSET UNIV : \E y \in UNIV : y \notin S

\* ----------------------------------------------------------------------
\* The module does not require any additional operators for the .cfg
\* ----------------------------------------------------------------------
=============================================================================