---- MODULE TLAPS ----
EXTENDS Integers

\* Backend provers for TLAPS: each operator below is a pragma that directs
\* the proof system to hand a subgoal to a specific prover with the
\* given timeout and optional tactic.  The operators are pure syntactic
\* placeholders here; they carry no runtime semantics inside the TLC
\* model, but their presence in the module names the provers the system
\* is allowed to use.
Zenon(n, t) == TRUE
Isabelle(n, t) == TRUE
CVC3(n, t) == TRUE
Yices(n, t) == TRUE
VeriT(n, t) == TRUE
Z3(n, t) == TRUE
SPASS(n, t) == TRUE
LS4(n) == TRUE

\* Temporal-logic proof rules from Lamport's 'The Temporal Logic of
\* Actions' -- reserved names for the proof system; they do not take
\* effect in this state-transition model.
INVARIANT(f) == TRUE
WFIS(f) == TRUE
SFIS(f) == TRUE
WF(f) == TRUE
SF(f) == TRUE

\* Foundational theorems that every TLA+ development uses: set
\* extensionality and the fact that no set of values is universal.
SetExtensionality == \A X, Y \in SUBSET Int : (\A x \in Int : x \in X <=> x \in Y) => X = Y
Univ != SUBSET Int

====