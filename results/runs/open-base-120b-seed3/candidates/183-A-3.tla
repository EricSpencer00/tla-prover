---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Backend prover configuration (timeouts in seconds)
\* ----------------------------------------------------------------------
CONSTANTS ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
          VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

\* Default timeout values – can be overridden by a TLC configuration file
ZenonTimeout   == 30
IsabelleTimeout == 30
CVC3Timeout    == 30
YicesTimeout   == 30
VeriTTimeout   == 30
Z3Timeout      == 30
SPASSTimeout   == 30
LS4Timeout     == 30

\* ----------------------------------------------------------------------
\* Backend dispatch operators (no operational effect, only for TLAPS)
\* ----------------------------------------------------------------------
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\* ----------------------------------------------------------------------
\* Fundamental set theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S : S # UNIV

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (provided as axioms so their names are
\* reserved for future use)
\* ----------------------------------------------------------------------
AXIOM InvarianceRule ==
  \A Inv, Init, Next :
    (Init => Inv) /\ (Inv /\ [Next]_vars => Inv) => []Inv

AXIOM WellFormednessRule ==
  \A P :
    (P => []P)   \* placeholder – real rule defined in the TLAPS library

AXIOM WeakFairnessRule ==
  \A F, Init, Next :
    (Init => <>[]F) => WF_vars(F)

AXIOM StrongFairnessRule ==
  \A F, Init, Next :
    (Init => []<>F) => SF_vars(F)

\* ----------------------------------------------------------------------
\* Specification skeleton required by the (empty) .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====