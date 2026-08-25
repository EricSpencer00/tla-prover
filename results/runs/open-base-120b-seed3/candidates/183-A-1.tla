---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* --------------------------------------------------------------------
   Backend pragmas for TLAPS.  Each operator is a placeholder that the
   proof system recognizes and replaces with a call to the corresponding
   automated prover or SMT solver.  The argument *p* can be used to pass
   options such as time‑outs or tactics.
   -------------------------------------------------------------------- *)

Zenon(p)   == TRUE
Isabelle(p) == TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

(* --------------------------------------------------------------------
   Fundamental set theorems that are always available in the library.
   -------------------------------------------------------------------- *)

SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    ( (\A x \in A : x \in B) /\ (\A x \in B : x \in A) ) => A = B

NoSetContainsAllValues ==
  \A S \in SUBSET UNIV :
    ~ ( \A x \in UNIV : x \in S )

(* --------------------------------------------------------------------
   Temporal‑logic proof rules (names reserved for future use).  Each
   rule is given as a trivially true operator; the real content is
   supplied by the TLAPS backend.
   -------------------------------------------------------------------- *)

Invariance ==
  \A P \in [UNIV -> BOOLEAN] : TRUE

WellFormedness ==
  \A A \in UNIV : TRUE

StrongFairness ==
  \A f \in UNIV : TRUE

WeakFairness ==
  \A f \in UNIV : TRUE

StepSimulation ==
  \A s, t \in UNIV : TRUE

====