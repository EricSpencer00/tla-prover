---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Backend pragma operators – they simply return their argument.  The
   actual dispatch to external provers is performed by the TLAPS
   tool, not by the TLA+ model itself.
   ---------------------------------------------------------------------- *)

Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule placeholders.  They are defined as the
   constant TRUE so that they can be referenced without causing an
   undefined‑identifier error.
   ---------------------------------------------------------------------- *)

InvariantRule        == TRUE
WellFormednessRule   == TRUE
StrongFairnessRule   == TRUE
WeakFairnessRule     == TRUE
StepSimulationRule   == TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems required by the description.
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====