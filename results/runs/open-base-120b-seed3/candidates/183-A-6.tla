---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

(* ----------------------------------------------------------------------
   Backend prover operators – these are placeholders that simply return
   their argument.  In practice they are used as pragmas by TLAPS.
   ---------------------------------------------------------------------- *)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule placeholders.  They are defined as identity
   operators so that their names can be reserved for future use.
   ---------------------------------------------------------------------- *)
Invariance(p) == p
WellFormed(p) == p
StrongFairness(p) == p
WeakFairness(p) == p
StepSimulation(p) == p

(* ----------------------------------------------------------------------
   Fundamental theorems required by the description.
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) \equiv (x \in T)) => S = T

THEOREM NoUniversalSet ==
  ~\E S \in SUBSET UNIV : \A x \in UNIV : x \in S

====