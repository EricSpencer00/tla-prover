---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  veriT,
  Z3,
  SPASS,
  LS4

\* Goal: document the backends TLAPS may dispatch a proof obligation to, and
\* the core temporal-logic proof rules it supports.  No state changes here;
\* this is pure infrastructure description.
SpecGoal == "Dispatching to theorem provers / SMT solvers and naming core TLAPS temporal proof rules."

INIT == SpecGoal

Next == SpecGoal

\* Two foundational facts that every TLA+ development rests on.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)
NoSetContainsAll == \A A \subseteq Nat : (\A x \in Nat : x \in A) => (Nat \subseteq A)

\* Reserved names of the core proof rules from Lamport's 'Temporal Logic of Actions'.
TemporalRules == {"invariance", "wellformed", "SF", "WF"}

====