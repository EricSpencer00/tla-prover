---- MODULE TLAPS ----
\*=====================================================================
\* TLAPS: Configuration module for the TLA+ Proof System.
\* It defines backend prover operators and fundamental temporal logic
\* proof rules, together with two basic set-theoretic theorems.
\*=====================================================================

\*-----------------------------
\* Backend prover dispatchers
\*-----------------------------
\* Each operator simply returns its argument; the proof manager
\* interprets the operator name to invoke the appropriate prover.
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\*-----------------------------
\* Temporal‑logic proof rules
\*-----------------------------
\* The following are placeholders for the well‑known rules from
\* Lamport’s *The Temporal Logic of Actions*.  Their bodies are
\* trivially TRUE; the proof system treats the names specially.
InvarianceRule   == TRUE
WellFormedness   == TRUE
StrongFairness   == TRUE
WeakFairness     == TRUE
StepSimulation    == TRUE

\*-----------------------------
\* Fundamental set theorems
\*-----------------------------
THEOREM SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x \in UNIV : (x \in A) <=> (x \in B)) => A = B

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

====