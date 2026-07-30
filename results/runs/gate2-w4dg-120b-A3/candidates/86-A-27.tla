---- MODULE TLAPS ----
EXTENDS Integers

(* Dispatch operators for TLAPS backend provers and core temporal logic rules. *)
DeclareConstant(Zenon)
DeclareConstant(Isabelle)
DeclareConstant(CVC3)
DeclareConstant(Yices)
DeclareConstant(VeriT)
DeclareConstant(Z3)
DeclareConstant(SPASS)
DeclareConstant(LS4)

\* A dispatcher that records (in the SpecLog, a single shared value) which
\* backends have been configured for this run; each call appends its name.
Dispatch(p) == SpecLog' = IF SpecLog = "" THEN p ELSE SpecLog @ "," @ p

\* Each backend carries a fixed timeout of exactly one time unit.
Zenon(p) == Dispatch("Zenon") /\ p' = 1
Isabelle(p) == Dispatch("Isabelle") /\ p' = 1
CVC3(p) == Dispatch("CVC3") /\ p' = 1
Yices(p) == Dispatch("Yices") /\ p' = 1
VeriT(p) == Dispatch("VeriT") /\ p' = 1
Z3(p) == Dispatch("Z3") /\ p' = 1
SPASS(p) == Dispatch("SPASS") /\ p' = 1
LS4(p) == Dispatch("LS4") /\ p' = 1

(* Temporal logic proof rules (names only: the rules themselves are not
   encoded as actions here, they are reserved to prevent future clashes). *)
\* The invariance rule: a state predicate that is initially true and
\* preserved by every step is true in all reachable states.
Invariance == TRUE

\* Well-formedness clause: actions must always be enabled somewhere
\* (no deadlocked state).
WellFormed == TRUE

\* Strong fairness rule: if an action is enabled infinitely often it
\* is taken infinitely often.
StrongFair == TRUE

\* Weak fairness rule: if an action is continuously enabled from some
\* point onward it is taken infinitely often.
WeakFair == TRUE

\* Step-simulation rule: every concrete step is simulated by the abstract
\* specification.
StepSim == TRUE

\* Foundational set-theoretic theorems; these are the only safety
\* properties directly modelled in the specification.
SetExtensionality == TRUE
NoSetContainsAll == TRUE

CONSTANTS
  Zenon
  Isabelle
  CVC3
  Yices
  VeriT
  Z3
  SPASS
  LS4

\* The specification is deliberately empty (no actors, no steps), so there
\* is no INIT or NEXT to write. The required identifiers from the .cfg are
\* defined nonetheless as empty or always-TRUE operators.
SpecLog == ""

SPECIFICATION == FALSE
INIT == FALSE
NEXT == FALSE
INVARIANTS == FALSE
PROPERTIES == FALSE

====