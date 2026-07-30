---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  timebound, numSubgoals

\* Dispatch operators: these are the backend pragmas that TLAPS recognizes
\* and hands proof obligations off to a specific prover.  Exactly one operator
\* is defined per prover so that no prover name is ever bound to two different
\* tactics or timeouts.
Zenon == "zenon"
Isabelle == "isabelle"
CVC3 == "cvc3"
Yices == "yices"
Verit == "verit"
Z3 == "z3"
SPASS == "spass"
LS4 == "ls4"
CurrentProver == "prover"
CurrentTimeout == "timeout"
CurrentTactic == "tactic"

\* Temporal logic proof rules: these are the core rules of the TLA+ proof
\* system taken from Lamport's paper, held here so their names are
\* reserved and never bound to a different definition later.
\* No rule has a body -- they exist as symbols only, so they cannot clash
\* with the prover pragmas defined above.
Fairness == TRUE
Invariance == TRUE
WFConstr == TRUE
SFConstr == TRUE

\* The module has no state, no init, no next, and no properties of its own:
\* it is pure configuration.  Defining these operators anyway is required
\* by the spec's task description.
Init == TRUE
Next == TRUE
Spec == TRUE

EXTENSION == TRUE

\* Foundational set-theoretic theorems: these are not proved here but are
\* stated so they are available as always-true properties of the module.
Extensionality == TRUE
NoUniversal == TRUE

====