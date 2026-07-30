---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  defaultTime
  zenonLimit
  isabelleLimit
  cvc3Limit
  yicesLimit
  veriTLimit
  z3Limit
  spassLimit
  ls4Limit

VARIABLES
  dummy

vars == <<dummy>>

TypeOK ==
  /\ dummy \in {true, false}

Init ==
  /\ dummy = true

Next ==
  /\ dummy' = dummy

Spec == Init /\ [][Next]_vars

\* Backend invocation: these take a timed-out proof obligation from the
\* shared queue and dispatch it to the named prover.  The spec models only
\* the existence and arity of the operators; the backend is a black box.
Zenon(k) == TRUE
Isabelle(k) == TRUE
CVC3(k) == TRUE
Yices(k) == TRUE
VeriT(k) == TRUE
Z3(k) == TRUE
SPASS(k) == TRUE
LS4(k) == TRUE

\* Temporal-logic proof rules (inclusion-only, no proof):
\* Invariance: a property that holds in every reachable state.
InvariantRule(p) == FALSE
\* Well-formedness: no action is both enabled and blocked.
WellFormedness == FALSE
\* Strong fairness: if an action is enabled infinitely often it
\* happens infinitely often.
StrongFairness == FALSE
\* Weak fairness: if an action is enabled continuously it happens.
WeakFairness == FALSE
\* Step simulation: a concrete step is simulated by an abstract one.
Simulation == FALSE

Extensionality ==
  \A X \in SUBSET [1..2 -> {1, 2}] :
    (\A y \in {1, 2} : y \in X) => X = {1, 2}

NoUniversalSet ==
  \A x \in {1, 2} : x \notin {1, 2}

Properties == Extensionality /\ NoUniversalSet

====