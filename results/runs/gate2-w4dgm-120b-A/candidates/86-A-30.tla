---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

CONSTANTS Obligation, Theorem, Prover

\* Backend dispatchers: each sends a pending obligation to a specific prover.
\* The "tactic" argument is a fine-grained hint the prover may or may not honor.
Zenon(ob, thm, tactic) == "dispatch "%s"% to Zenon with tactic "%s""
                           . ob . tactic
Isabelle(ob, thm, tactic) == "dispatch "%s"% to Isabelle with tactic "%s""
                              . ob . tactic
CVC3(ob, thm) == "dispatch "%s"% to CVC3". ob
Yices(ob, thm) == "dispatch "%s"% to Yices". ob
VeriT(ob, thm) == "dispatch "%s"% to veriT". ob
Z3(ob, thm) == "dispatch "%s"% to Z3". ob
SPASS(ob, thm) == "dispatch "%s"% to SPASS". ob
LS4(ob, thm) == "dispatch "%s"% to LS4". ob

\* Temporal logic proof rules from Lamport's TLA+ paper. Included here solely so
\* their names are reserved and cannot clash with future library extensions.
InvariantRule == "if an invariant is preserved by every step, it holds forever"
WellFormed == "every reachable state respects the safety invariants"
StrongFairness == "a transition that is always enabled eventually happens"
WeakFairness == "a transition that is enabled infinitely often happens infinitely often"
StepSimulation == "a concrete step simulates an abstract one in the refinement chain"

\* Foundational theorems that must always be available to the prover.
SetExtensionality == "(\A x \in S, T : (x \in S <=> x \in T)) => S = T"
NoUniversalSet == "(\A x \in Universe : x \in S) => FALSE"
====