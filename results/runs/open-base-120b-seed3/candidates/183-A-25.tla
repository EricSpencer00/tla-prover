---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Backend dispatch operators for TLAPS.  Each simply returns its
  argument; the name is used by the proof manager to select a
  prover or solver.
-----------------------------------------------------------------*)
Zenon(p_)      == p
Isabelle(p_)   == p
CVC3(p_)       == p
Yices(p_)      == p
VeriT(p_)      == p
Z3(p_)         == p
SPASS(p_)      == p
LS4(p_)        == p

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule placeholders.  In a real development
  these would be defined by the corresponding proof steps.
-----------------------------------------------------------------*)
InvariantRule(Inv_)          == TRUE
WellFormedRule(Stmt_)        == TRUE
StrongFairnessRule(Cond_)    == TRUE
WeakFairnessRule(Cond_)      == TRUE
StepSimulationRule(Src_, Tgt_) == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

(*-----------------------------------------------------------------
  Place‑holder identifiers required by the generic configuration.
-----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT           == TRUE
NEXT           == TRUE
INVARIANTS     == {}
PROPERTIES     == {}

====