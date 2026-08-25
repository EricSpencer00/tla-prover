---- MODULE TLAPS ----
EXTENDS Integers, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Backend prover dispatch operators.  These are placeholders that
   TLAPS recognises as directives to the named provers; here they are
   defined as identity operators for syntactic completeness.
   ---------------------------------------------------------------------- *)

Zenon(p, timeout) == p
Isabelle(p, timeout) == p
CVC3(p, timeout) == p
Yices(p, timeout) == p
VeriT(p, timeout) == p
Z3(p, timeout) == p
SPASS(p, timeout) == p
LS4(p, timeout) == p

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule placeholders.  Their names are reserved so
   that future modules can refer to them without risk of clash.
   ---------------------------------------------------------------------- *)

Invariance(rule) == TRUE
WellFormedness(rule) == TRUE
StrongFairness(rule) == TRUE
WeakFairness(rule) == TRUE
StepSimulation(rule) == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems.
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET UNIV :
    \E x \in UNIV : x \notin S

====