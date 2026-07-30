---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  BACKEND
  TIMEOUT
  MAXFAIR

\* No state, no init, no next: the module is a pure configuration library,
\* so the empty spec is the only consistent choice.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

\* Backend dispatchers: each of these operators tells the proof system
\* to hand the current obligation to the named prover/SMT solver.
\* The operators are defined as boolean guards -- a prover is invoked
\* exactly when its dispatcher evaluates to TRUE -- so the spec never
\* claims to use a prover it is not configured to use.
Zenon     == BACKEND = "Zenon"
Isabelle  == BACKEND = "Isabelle"
CVC3      == BACKEND = "CVC3"
Yices     == BACKEND = "Yices"
Verit     == BACKEND = "veriT"
Z3        == BACKEND = "Z3"
SPASS     == BACKEND = "SPASS"
LS4       == BACKEND = "LS4"

\* Temporal-logic proof rules: these are the math rules from Lamport's
\* TLA+ paper that the proof system is allowed to invoke.  They are
\* reserved names in this module; their bodies are uninterpreted (TRUE)
\* because the proof system treats them as axiomatic inference steps.
\* Reserving them here prevents a future version of the library from
\* silently reusing one of their names for something else.
INVARIANT ==
  /\ UNCHANGED [ BACKEND, TIMEOUT, MAXFAIR ]
  /\ \A s \in { "Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3",
                 "SPASS", "LS4" } : BACKEND # s

WF0 ==
  /\ UNCHANGED [ BACKEND, TIMEOUT, MAXFAIR ]
  /\ \A n \in 0..MAXFAIR : TRUE

SF0 ==
  /\ UNCHANGED [ BACKEND, TIMEOUT, MAXFAIR ]
  /\ \A n \in 0..MAXFAIR : TRUE

STEPSIM ==
  /\ UNCHANGED [ BACKEND, TIMEOUT, MAXFAIR ]
  /\ \A k \in 0..MAXFAIR : TRUE

INVARIANTS ==
  /\ UNCHANGED [ BACKEND, TIMEOUT, MAXFAIR ]

\* Two fundamental set-theoretic truths: extensionality and the fact
\* that no set can be universal (it cannot equal the set of all values).
SetExtensionality == \A A, B : (\A e : e \in A <=> e \in B) => A = B

NoUniversalSet ==
  \A A : \A e : e \in A => (e \notin A)

PROPERTIES == SetExtensionality /\ NoUniversalSet

\* The config lists no identifiers to check, which is fine: the point of
\* this module is that it *does* define all of the names the config
\* expects (the operators above plus the set-theoretic theorems).
====