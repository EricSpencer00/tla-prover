---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Backend provers and SMT solvers.
\* These operators are only placeholders used by TLAPS
\* to control which external prover is invoked for a
\* given proof obligation.  Their arguments are not used
\* during model checking.
\* -------------------------------------------------
Zenon(expr, \* timeout in seconds
      timeout) == TRUE
Isabelle(expr, timeout) == TRUE
CVC3(expr, timeout) == TRUE
Yices(expr, timeout) == TRUE
veriT(expr, timeout) == TRUE
Z3(expr, timeout) == TRUE
SPASS(expr, timeout) == TRUE
LS4(expr, timeout) == TRUE

\* -------------------------------------------------
\* Temporal logic proof rules (place‑holders).
\* The names are reserved so that future modules can
\* refer to them without clash.
\* -------------------------------------------------
Invariance(Inv, Init, Next) == 
    /\ Inv \in BOOLEAN
    /\ Init => Inv
    /\ \A s, s' : (Next(s,s') /\ Inv) => Inv

WellFormedness(Formula) == TRUE

StrongFairness(Cond, Action) == TRUE
WeakFairness(Cond, Action) == TRUE

StepSimulation(Spec1, Spec2) == TRUE

\* -------------------------------------------------
\* Fundamental set theorems.
\* -------------------------------------------------
SetExtensionality == 
    \A S, T \in SUBSET UNIV :
        (\A x : (x \in S) \iff (x \in T)) => S = T

NoUniversalSet == 
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* Theorems are asserted as facts for TLAPS.
THEOREM SetExtensionality
THEOREM NoUniversalSet

====