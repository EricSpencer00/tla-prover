---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, Integers, Reals

\* ----------------------------------------------------------------------
\* Backend pragma placeholders for the TLAPS proof system.
\* These operators have no operational effect; they exist solely to
\* reserve the names used by TLAPS when dispatching obligations to
\* various automated provers and SMT solvers.
\* ----------------------------------------------------------------------
Zenon(p)   == TRUE
Isabelle(p)== TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

\* ----------------------------------------------------------------------
\* Fundamental set‑theoretic theorems used throughout the proof library.
\* ----------------------------------------------------------------------
CONSTANT UNIV

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) = (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV :
    ~(\A x \in UNIV : x \in S)

====