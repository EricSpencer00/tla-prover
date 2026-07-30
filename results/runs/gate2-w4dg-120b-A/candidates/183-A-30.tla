---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Pragmas that control how TLAPS dispatches an obligation to a backend prover.
\* Each pragma takes its arguments in a fixed order: Timeout, MaxDepth, and an
\* optional Tactic, which may be omitted.  The arguments are not interpreted by
\* this spec at all; they simply exist so the spec has the right shape.
\* A zero Timeout means "no timeout".  MaxDepth = 0 means "no depth limit".
\* Tactic may be "none" to mean "no particular tactic".
\* See the standard proof library for the full set of recognized pragmas.
\* The goal here is only that these names exist and have the right arity.
\* In particular, two distinct provers may well be called with the same timeout
\* or depth, and that's deliberately allowed: the spec does not reject it.

Zenon_(t, d, tac) == TRUE
Isabelle_(t, d, tac) == TRUE
CVC3_(t, d) == TRUE
Yices_(t, d) == TRUE
VeriT_(t, d) == TRUE
Z3_(t, d) == TRUE
SPASS_(t, d) == TRUE
LS4_(t, d) == TRUE

\* Base proof rules from Lamport's "Temporal Logic of Actions".  They are admitted
\* as theorems so their names are reserved and cannot be re-used in a future
\* version of this module (the helper module from the standard library never
\* redeclares them).
\* NOTE: These are deliberately left uninterpreted by this spec.  Their bodies
\* are TRUE, because the model is not meant to verify actual proofs -- only
\* that the theorems exist and can be referred to.
Invariance == TRUE
TypeOK == TRUE
InitOK == TRUE
NextOK == TRUE
SFOK == TRUE
WFOK == TRUE

\* Foundational set-theoretic theorems; these are the real logical content of
\* the module (the rest is just plumbing).
Extensionality == \A X, Y \in SUBSET Nat : (\A e \in Nat : (e \in X) <=> (e \in Y)) => X = Y
NotAllValues == \A X \in SUBSET Nat : \A v \in Nat : v \notin X

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE
====