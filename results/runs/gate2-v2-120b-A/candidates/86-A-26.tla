---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Configuration for TLAPS backend provers (no actual variables or state)
\* ----------------------------------------------------------------------

\* Prover identifiers (constants) – they are only names, not used in the model
Zenon   == "Zenon"
Isabelle == "Isabelle"
CVC3    == "CVC3"
Yices   == "Yices"
VeriT   == "veriT"
Z3      == "Z3"
SPASS   == "SPASS"
LS4     == "LS4"

\* ----------------------------------------------------------------------
\* Timeouts and tactics (also constants, not used further)
\* ----------------------------------------------------------------------
ZenonTimeout   == 10
IsabelleTimeout == 10
CVC3Timeout    == 10
YicesTimeout   == 10
VeriTTimeout   == 10
Z3Timeout      == 10
SPASSTimeout   == 10
LS4Timeout     == 10

ZenonTactic    == "default"
IsabelleTactic == "default"
CVC3Tactic     == "default"
YicesTactic    == "default"
VeriTTactic    == "default"
Z3Tactic       == "default"
SPASSTactic    == "default"
LS4Tactic      == "default"

\* ----------------------------------------------------------------------
\* No state variables – the model is empty (the "Spec" is simply TRUE)
\* ----------------------------------------------------------------------
VARIABLES

\* ----------------------------------------------------------------------
\* SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE

Init == TRUE

Next  == TRUE

\* Safety theorem: set extensionality
Extensionality ==
  \A A, B \subseteq SUBSET UNIV :
    (\A x \in UNIV : x \in A <=> x \in B) => A = B

\* Safety theorem: no set contains every possible value
NoUniversalSet ==
  \A S \subseteq UNIV : ~ (UNIV \subseteq S)

INVARIANTS == Extensionality

PROPERTIES == NoUniversalSet

\* ----------------------------------------------------------------------
\* Export the required identifiers
\* ----------------------------------------------------------------------
THEOREM ExtensionalityTheorem == Extensionality
THEOREM NoUniversalSetTheorem == NoUniversalSet

====