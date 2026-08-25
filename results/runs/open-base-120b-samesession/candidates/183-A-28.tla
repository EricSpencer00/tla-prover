---- MODULE TLAPS ----
EXTENDS TLC

\* ----------------------------------------------------------------------
\* Backend provers (place‑holder identifiers for TLAPS configuration)
\* ----------------------------------------------------------------------
Zenon      == "zenon"
Isabelle   == "isabelle"
CVC3       == "cvc3"
Yices      == "yices"
VeriT      == "verit"
Z3         == "z3"
SPASS      == "spass"
LS4        == "ls4"

\* Optional timeout parameters (in seconds)
ZenonTimeout    == 30
IsabelleTimeout == 30

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (place‑holders)
\* ----------------------------------------------------------------------
InvariantRule(P(_)) == 
  (* Invariance: if P holds initially and is preserved by every step,
     then []P holds.  The actual proof rule is supplied by TLAPS. *)
  TRUE

WellFormednessRule == 
  (* Well‑formedness of actions and state predicates. *)
  TRUE

StrongFairness(P(_)) == 
  (* Strong fairness: if an enabled action occurs infinitely often,
     then its effect occurs infinitely often. *)
  TRUE

WeakFairness(P(_)) == 
  (* Weak fairness: if an action is continuously enabled, it eventually occurs. *)
  TRUE

StepSimulation == 
  (* Step‑simulation rule for refinement proofs. *)
  TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality == 
  \A X, Y \in SUBSET UNIV :
    (\A e \in UNIV : (e \in X) \<=> (e \in Y)) => X = Y

NoUniversalSet == 
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

=============================================================================