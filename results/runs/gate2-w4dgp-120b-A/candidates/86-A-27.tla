---- MODULE TLAPS ----
\* Backend provers: This module defines the TLAPS pragmas for selecting which
\* automated prover backs each proof obligation. It also lists the core
\* temporal-logic proof rules so their names are reserved and cannot clash.
EXTENDS Naturals

\* Zenon is a tableau prover for first-order logic with equality and choice.
Zenon == "zenon"
\* Isabelle/HOL is a higher-order interactive prover with a built-in arithmetic
\* tactic, invoked here with a timeout of 20 seconds.
Isabelle == "isabelle -C -t 20"
\* CVC3 is an SMT solver offering arithmetic, arrays, and uninterpreted
\* functions. Its Heartbeat flag must be kept enabled for it to stay responsive.
CVC3 == "cvc3 -heartbeat"
\* Yices is another SMT solver, and its arithmetic rewriter may be switched off
\* if it interferes with a particular proof.
Yices == "yices"
\* veriT is a SAT modulo theories solver, used here for pure propositional
\* reasoning; its tactic is set to \sigma (the strongest complete strategy).
veriT == "verit -t sigma"
\* Z3 is a widely-used SMT-solver with a configurable arithmetic solver.
Z3 == "z3 -arith"
\* SPASS is another propositional SAT solver, here run with the -tac switch.
SPASS == "spass -tac"
\* The LS4 prover handles the temporal operators in the TLA+ logic.
LS4 == "ls4"

\* Invariance: a semantic safety rule stating that whenever an invariant is
\* asserted it must hold throughout all reachable states.
InvariantRule == TRUE
\* Well-formedness: a rule that every constant introduced by the system has
\* a concrete value in the model's domain.
WellFormedRule == TRUE
\* Strong fairness: a rule governing persistence of actions under strong
\* fairness, which is strictly stronger than the rule below.
StrongFairnessRule == TRUE
\* Weak fairness: a rule governing persistence of actions under weak
\* fairness, weaker but more commonly usable than strong fairness.
WeakFairnessRule == TRUE

\* Extensionality: two sets are equal if and only if they have exactly the
\* same elements, each of which puts an element of the other inside.
Extensionality == \A x \in X : x \in Y <=> x \in Z
\* Boundedness: no set in the system can contain every possible value.
Boundedness == \A x \in S : x \notin S
====