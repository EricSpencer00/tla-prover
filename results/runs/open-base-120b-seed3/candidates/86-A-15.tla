---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANT V \* an arbitrary (non‑empty) set of values

\* -----------------------------------------------------------------
\* Fundamental theorems required by the description
\* -----------------------------------------------------------------

SetExtensionality ==
    \A S, T \in SUBSET V :
        (\A x \in V : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S \in SUBSET V :
        ~(\A x \in V : x \in S)

\* -----------------------------------------------------------------
\* Place‑holder operators required by the configuration file
\* -----------------------------------------------------------------

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====