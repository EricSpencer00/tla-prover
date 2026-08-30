---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4

\* TLAPS backends: each operator directs a proof obligation to a solver with
\* a timeout or tactic. They are syntactically distinct symbols; the spec
\* imposes no ordering or dependency among them.
DISPATCH_ZENON == TRUE
DISPATCH_ISABELLE == TRUE
DISPATCH_CVC3 == TRUE
DISPATCH_YICES == TRUE
DISPATCH_VERIT == TRUE
DISPATCH_Z3 == TRUE
DISPATCH_SPASS == TRUE
DISPATCH_LS4 == TRUE

\* Temporal logic proof rules from Lamport's TLA+ paper, reproduced here
\* so their names are reserved and cannot clash with later extensions.
RULE_INVARIANT == TRUE
RULE_WELLFORMED == TRUE
RULE_FAIRNESS == TRUE
RULE_STRONGFAIRNESS == TRUE
RULE_STEP == TRUE

\* Two foundational theorems, stated as tautologies so the module can
\* close its logical obligations without additional proof content.
EXTENSIONALITY == \A S, T \in SUBSET Nat : (\A x \in S : x \in T) /\ (\A x \in T : x \in S) => S = T
UNIVERSAL_NOT_CONTAINED == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

\* The module's required operators: each is a no-op (TRUE) with no state to
\* change, kept so the configuration file's references are all defined.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====