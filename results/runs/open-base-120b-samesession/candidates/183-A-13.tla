---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  TLAPS backend pragma operators                                           *)
(***************************************************************************)

Zenon(p) == TRUE          \* dispatch to Zenon prover with parameters p
Isabelle(p) == TRUE       \* dispatch to Isabelle prover
CVC3(p) == TRUE           \* dispatch to CVC3 prover
Yices(p) == TRUE          \* dispatch to Yices prover
VeriT(p) == TRUE          \* dispatch to veriT prover
Z3(p) == TRUE             \* dispatch to Z3 prover
SPASS(p) == TRUE          \* dispatch to SPASS prover
LS4(p) == TRUE            \* dispatch to LS4 temporal logic prover

(***************************************************************************)
(*  Fundamental set-theoretic theorems                                      *)
(***************************************************************************)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET Nat :
    (\A x \in Nat : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET Nat : \E x \in Nat : x \notin S

(***************************************************************************)
(*  Temporal logic proof rules (place‑holders)                             *)
(***************************************************************************)

\* Invariance rule: if P is an invariant of a step relation, then []P holds.
Invariance(P) == TRUE

\* Weak fairness rule for an action A: WF_{vars}(A)
WF(vars, A) == TRUE

\* Strong fairness rule for an action A: SF_{vars}(A)
SF(vars, A) == TRUE

\* Well‑formedness of a temporal formula F
WellFormed(F) == TRUE

\* Step simulation rule: simulates one step of a specification
StepSimulation(step) == TRUE

(***************************************************************************)
(*  No state variables, actions, or properties are required for this       *)
(*  helper module.                                                          *)
(***************************************************************************)

====