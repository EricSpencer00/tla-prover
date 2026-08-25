---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS.  These operators are only used as
\* pragmas in proofs; they simply return their argument.
\* ----------------------------------------------------------------------
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (place‑holders).  Their names are reserved
\* to avoid clashes with future versions of the library.
\* ----------------------------------------------------------------------
InvarianceRule(Inv, Init, Next) ==
  (* If Init implies Inv and Inv is preserved by Next, then Inv holds always. *)
  TRUE

WellFormednessRule(Init, Next) ==
  (* The initial condition and the next‑state relation are well‑formed. *)
  TRUE

StrongFairnessRule(Fair, Next) ==
  (* Strong fairness for the action described by Fair under Next. *)
  TRUE

WeakFairnessRule(Fair, Next) ==
  (* Weak fairness for the action described by Fair under Next. *)
  TRUE

StepSimulationRule(Sim, Init, Next) ==
  (* Step‑simulation between two specifications. *)
  TRUE

\* ----------------------------------------------------------------------
\* Fundamental set‑theoretic theorems.
\* ----------------------------------------------------------------------
CONSTANT Universe

THEOREM SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x \in Universe : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET Universe : \E x \in Universe : x \notin S

====