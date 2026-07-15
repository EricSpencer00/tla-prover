---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  TLAPS: Backend pragmas and basic temporal logic proof rules for TLAPS  *)
(*  This module does not describe a concrete system state. It provides    *)
(*  operators that represent backend prover configuration and fundamental *)
(*  proof-theoretic theorems used by the TLA+ Proof System.               *)
(***************************************************************************)

\* ------------------------------------------------------------------------
\* Backend configuration operators (place‑holders for actual TLAPS pragmas)
\* ------------------------------------------------------------------------

\* Dispatch proof obligations to various automated theorem provers
Zenon   == "zenon"   \* (placeholder string identifying the prover)
Isabelle== "isabelle"
CVC3    == "cvc3"
Yices   == "yices"
VeriT   == "verit"
Z3      == "z3"
SPASS   == "spass"
LS4     == "ls4"

\* Time‑out and tactic parameters (illustrative, not used in the model)
ZenonTimeout    == 30
IsabelleTimeout == 30
CVC3Timeout     == 30
YicesTimeout    == 30
VeriTTimeout    == 30
Z3Timeout       == 30
SPASSTimeout    == 30
LS4Timeout      == 30

\* ------------------------------------------------------------------------
\* Fundamental temporal‑logic proof rules (names reserved for TLAPS)
\* ------------------------------------------------------------------------

\* Invariance rule
InvRule(Term) == Term

\* Well‑formedness rule
WellFormed(Term) == Term

\* Strong fairness rule
StrongFair(Term) == Term

\* Weak fairness rule
WeakFair(Term) == Term

\* Step simulation rule
StepSim(Term) == Term

\* ------------------------------------------------------------------------
\* Safety theorems required by the description
\* ------------------------------------------------------------------------

\* Set extensionality: two sets are equal iff they have the same elements
Extensionality == 
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

\* No set contains every possible value (over Nat)
NoUniversalSet == 
  \A S \in SUBSET Nat : ~(\A x \in Nat : x \in S)

\* ------------------------------------------------------------------------
\* Specification skeleton (required identifiers, though no concrete state)
\* ------------------------------------------------------------------------

CONSTANT defaultInit, defaultNext, defaultInv, defaultProp

\* SPECIFICATION is a record collecting the main operators
SPECIFICATION == [Init |-> defaultInit,
                  Next |-> defaultNext,
                  Inv  |-> defaultInv,
                  Prop |-> defaultProp]

\* Required identifiers: operators with exact names
INIT == defaultInit
NEXT == defaultNext
INVARIANTS == defaultInv
PROPERTIES == defaultProp

\* Provide trivial defaults so the module type‑checks
defaultInit == TRUE
defaultNext == FALSE
defaultInv  == TRUE
defaultProp == TRUE

=============================================================================