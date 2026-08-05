---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas for the TLA Proof System: these are not executable actions;
\* each names a prover or SMT-backend and the resource budget to allocate.
PROVER == "provers/zenon"
TIMEOUT == 30
ISAUTO == "provers/isabelle"
SMTC3 == "provers/cvc3"
SMTYICES == "provers/yices"
SMVERIT == "provers/verit"
SMTZ3 == "provers/z3"
SMTSPASS == "provers/spass"
PROVERLS4 == "provers/ls4"
TACTIC == "ls4/tactic"

\* No state to model: the module's sole role is to expose these names.
VARIABLES \* none

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<>>

\* Set extensionality: two sets are equal whenever they have the same elements.
Extensionality ==
  \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => (X = Y)

\* No set contains every natural number.
NoUniversalSet == \A X \in SUBSET Nat : X # Nat

====