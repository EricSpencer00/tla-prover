---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  Backend dispatch operators (place‑holders for TLAPS)                   *)
(***************************************************************************)

Zenon(ob) == TRUE
Isabelle(ob) == TRUE
CVC3(ob) == TRUE
Yices(ob) == TRUE
VeriT(ob) == TRUE
Z3(ob) == TRUE
SPASS(ob) == TRUE
LS4(ob) == TRUE

(***************************************************************************)
(*  Temporal‑logic proof‑rule operators (place‑holders)                    *)
(***************************************************************************)

(* Invariance rule:  if Init ⇒ P and  P ∧ [Next]_v ⇒ P' then  []P holds *)
InvarianceRule(P, Init, Next, v) == 
    /\ Init => P
    /\ (P /\ [Next]_v) => P'

(* Well‑formedness rule:  a specification is well‑formed if Init and Next *)
WellFormednessRule(Init, Next) == 
    /\ Init \in BOOLEAN
    /\ Next \in BOOLEAN

(* Strong fairness rule (SF):  if an action is enabled infinitely often,
   then it occurs infinitely often. *)
StrongFairnessRule(A, Enabled) == 
    []<>(Enabled) => []<>(A)

(* Weak fairness rule (WF):  if an action is continuously enabled, then it
   must eventually occur. *)
WeakFairnessRule(A, Enabled) == 
    []<>(Enabled) => []<>(A)

(* Step simulation rule:  a step of the implementation simulates a step of
   the specification. *)
StepSimulationRule(ImplStep, SpecStep) == 
    ImplStep => SpecStep

(***************************************************************************)
(*  Fundamental theorems                                                   *)
(***************************************************************************)

SetExtensionality == 
    \A A, B : (\A x : (x \in A) = (x \in B)) => A = B

NoUniversalSet == 
    ~\E S : \A x : x \in S

(***************************************************************************)
(*  No state variables, actions, or properties are required for this       *)
(*  configuration module.                                                  *)
(***************************************************************************)

====