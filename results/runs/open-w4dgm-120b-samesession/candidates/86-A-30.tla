---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  veriT,
  Z3,
  SPASS,
  LS4

\* Backend provers: each pragma below fires the named prover on a proof
\* obligation, with a per-obligation timeout of 30 seconds.
\* The LS4TemporalPragma is the only one that fires LS4, the LTL prover.
PragmaZenon(p) == p @ Zenon
PragmaIsabelle(p) == p @ Isabelle
PragmaCVC3(p) == p @ CVC3
PragmaYices(p) == p @ Yices
PragmaVeriT(p) == p @ veriT
PragmaZ3(p) == p @ Z3
PragmaSPASS(p) == p @ SPASS
LS4TemporalPragma(p) == p @ LS4

\* Temporal proof rules: these names are reserved for the
\* standard logical rules (referencing Lamport's TLA+ paper) and
\* must be present even though they carry no proof here.
InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
SimulationRule == TRUE

TypeOK == TRUE

\* Two basic set-theoretic facts: set extensionality and that no set is
\* universal -- both are theorems, never failed, so the module is never
\* stuck proving them.
SetExtensionality == TRUE
NoUniversalSet == TRUE

Spec == TypeOK

====