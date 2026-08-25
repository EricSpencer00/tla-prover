---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Backend pragma stubs for TLAPS.  These definitions have no effect on
\* the semantics of the specification; they simply provide names that
\* the proof system can refer to.
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
\* Fundamental theorems included in this module.
\* ----------------------------------------------------------------------

\* Set extensionality: two sets are equal iff they have the same elements.
SetExtensionality ==
  \A S, T : (\A x : (x \in S) \equiv (x \in T)) => S = T

\* No set contains every possible value (i.e., there is no universal set).
NoUniversalSet ==
  \A S : ~(\A x : x \in S)

====