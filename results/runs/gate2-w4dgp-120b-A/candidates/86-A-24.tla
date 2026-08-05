---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Pragmas that instruct the TLA Proof System which backend theorem prover to run
\* on each subgoal.  The arguments are the subgoal, a timeout in seconds, and an
\* optional tactic string.
Zenon(g, t) == TRUE
Isabelle(g, t) == TRUE
CVC3(g, t) == TRUE
Yices(g, t) == TRUE
VeriT(g, t) == TRUE
Z3(g, t) == TRUE
SPASS(g, t) == TRUE
\* LS4 is the name of the temporal-logic prover; it takes no timeout argument.
LS4(g) == TRUE

\* Foundational proof rules for temporal logic (invariance, fairness, etc.).
\* They are stated here, with no operational semantics attached, so that their
\* names are defined and reserved by the module without being used.
InvRule == TRUE
WFRule == TRUE
SFRule == TRUE
WFRule == TRUE

\* The empty set has no members, so its cardinality is zero.
Extensionality ==
  \A x, y \in SUBSET (Nat \cup Bool) : (x \subseteq y /\ y \subseteq x) => (x = y)

\* No set contains every possible value.
NotAllValues ==
  \A s \in SUBSET (Nat \cup Bool) : s # (Nat \cup Bool)
====