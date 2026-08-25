---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend pragmas for TLAPS: placeholders that direct proof obligations
\* to various automated provers and SMT solvers.  The definitions are
\* deliberately trivial; they exist solely to reserve the names.
\* ----------------------------------------------------------------------
Zenon(expr)    == TRUE
Isabelle(expr) == TRUE
CVC3(expr)     == TRUE
Yices(expr)    == TRUE
VeriT(expr)    == TRUE
Z3(expr)       == TRUE
SPASS(expr)    == TRUE
LS4(expr)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal logic proof rules (stubs).  The actual logical content is
\* defined elsewhere; here we only provide the identifiers.
\* ----------------------------------------------------------------------
Invariant(P)          == TRUE
WellFormed(P)         == TRUE
StrongFairness(A)     == TRUE
WeakFairness(A)       == TRUE
StepSimulation(Impl, Spec) == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A A, B : (\A x : (x \in A) <=> (x \in B)) => A = B

THEOREM NoUniversalSet ==
  \A S : S = UNIV => FALSE

====