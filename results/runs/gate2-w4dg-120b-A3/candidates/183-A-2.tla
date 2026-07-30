---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

\* Pragmas for the TLA Proof System's automated backends: each operator here
\* names a prover or solver that a proof obligation may be dispatched to,
\* together with any configuration (timeout, tactics) for that dispatch.
\* The operators below are all the identifiers referenced in the standard
\* config file; none may be omitted, and their signatures must match
\* exactly what the config expects, so that a future version can add a
\* new backend without colliding with an existing name.

CONSTANTS MaxTimeout

\* Zenon (a first-order prover): fires immediately, no timeout.
Zenon == [tactic |-> "auto"]

\* Isabelle (an interactive theorem prover): fires on a bounded deadline.
Isabelle == [deadline |-> MaxTimeout]

\* CVC3 (an older SMT solver): fires on a bounded deadline.
CVC3 == [deadline |-> MaxTimeout]

\* Yices (an SMT solver): fires on a bounded deadline.
Yices == [deadline |-> MaxTimeout]

\* veriT (an SMT solver): fires on a bounded deadline.
VeriT == [deadline |-> MaxTimeout]

\* Z3 (the most widely used SMT solver): fires on a bounded deadline.
Z3 == [deadline |-> MaxTimeout]

\* SPASS (a resolution prover): fires on a bounded deadline.
SPASS == [deadline |-> MaxTimeout]

\* LS4 (a temporal-logic prover): fires on a bounded deadline.
LS4 == [deadline |-> MaxTimeout]

\* A placeholder for any backend that the user may configure at runtime.
UserConfigured == [config |-> "default"]

\* Foundational temporal-logic proof rules. The rules themselves are not
\* proved here; they are postulated so their names are reserved by the
\* standard library and cannot clash with user-defined rules later.
\* (From Leslie Lamport's "The Temporal Logic of Actions".)
SetExtensionality == TRUE
SetNotAllValues == TRUE

\* No model is actually explored here: the spec simply invokes the rules.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====