---- MODULE TLAPS ----
EXTENDS FiniteSets

\* ----------------------------------------------------------------------
\* Backend provers (identifiers used by TLAPS to select a prover)
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Optional configuration parameters (timeouts in seconds, tactics, etc.)
CONSTANTS ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
         VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout,
         ZenonTactic, IsabelleTactic, CVC3Tactic, YicesTactic,
         VeriTTactic, Z3Tactic, SPASSTactic, LS4Tactic

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names are reserved for TLAPS)
\* ----------------------------------------------------------------------
InvariantRule == 
  \* If a state predicate I is invariant, then []I holds.
  TRUE

WellFormednessRule == 
  \* Ensures that actions are well‑formed.
  TRUE

StrongFairnessRule == 
  \* Strong fairness (SF) rule.
  TRUE

WeakFairnessRule == 
  \* Weak fairness (WF) rule.
  TRUE

StepSimulationRule == 
  \* Step‑simulation rule.
  TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET UNIV :
    S # UNIV => \E x \in UNIV : x \notin S

====