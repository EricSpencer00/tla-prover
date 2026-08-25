---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Backend prover identifiers (place‑holders for TLAPS configuration)
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Optional timeout parameters for the back‑ends
CONSTANTS ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
          VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

\* ----------------------------------------------------------------------
\* Pragmatic operators that stand for dispatching a proof obligation to a
\* particular automated prover.  In a real TLAPS library these would be
\* interpreted by the proof manager; here they are defined as trivial
\* true‑valued operators so that the module is syntactically complete.
\* ----------------------------------------------------------------------
Zenon(p)    == TRUE
Isabelle(p) == TRUE
CVC3(p)     == TRUE
Yices(p)    == TRUE
VeriT(p)    == TRUE
Z3(p)       == TRUE
SPASS(p)    == TRUE
LS4(p)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (names only, bodies are stubs)
\* ----------------------------------------------------------------------
Invariance(R)          == TRUE
WellFormedness(R)      == TRUE
StrongFairness(R)      == TRUE
WeakFairness(R)        == TRUE
StepSimulation(R, S)  == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A A, B : (\A x : (x \in A) <=> (x \in B)) => A = B

THEOREM NoUniversalSet ==
  \A S : ~ (\A x : x \in S)

====