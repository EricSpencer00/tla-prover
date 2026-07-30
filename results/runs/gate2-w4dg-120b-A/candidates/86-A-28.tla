---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
    zenon,
    isabelle,
    cvc3,
    yices,
    veriT,
    z3,
    spass,
    ls4

\* Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, and LS4 are the provers
\* that TLAPS may be instructed to invoke against a proof obligation.

\* Backends: each field gives the timeout (in seconds) to run the prover
\* for, and the tactic (or empty) that the backend was told to use.
Backends ==
    [ prover |-> zenon, timeout |-> 2, tactic |-> "" ]
    [ prover |-> isabelle, timeout |-> 2, tactic |-> "" ]
    [ prover |-> cvc3, timeout |-> 2, tactic |-> "" ]
    [ prover |-> yices, timeout |-> 2, tactic |-> "" ]
    [ prover |-> veriT, timeout |-> 2, tactic |-> "" ]
    [ prover |-> z3, timeout |-> 2, tactic |-> "" ]
    [ prover |-> spass, timeout |-> 2, tactic |-> "" ]
    [ prover |-> ls4, timeout |-> 2, tactic |-> "" ]

\* A proof step names the prover to be used, the current proof goal, and
\* a budget of solver steps to spend on it.
Steps == [ prover |-> zenon, goal |-> "goal", fuel |-> 1 ]

\* A dispatch table entry names the prover to use, the proof goal, and the
\* remaining solver steps still available to that proof.
Dispatch == [ prover |-> zenon, goal |-> "goal", fuel |-> 1 ]

\* The proof configuration is tuned by a per-prover timeout and a per-step
\* fuel budget, both of which must stay above zero.
SpecBudget == [ prover |-> zenon, timeout |-> 2, fuel |-> 1 ]

\* Rules of temporal logic that may be invoked by a proof. The invariance
\* rule lets the user assert a state predicate as an invariant. The
\* well-formedness rules let the user assert that a next-state relation
\* and a refinement map are well-formed. The strong and weak fairness
\* rules let the user assert fairness of a transition under strong or
\* weak fairness, and the step-simulation rule lets the user assert that
\* one specification step simulates another.
TemporalRules ==
    (invariantRule \in BOOLEAN) /\ (wfRule \in BOOLEAN) /\ (sfRule \in BOOLEAN)
    /\ (wfStep \in BOOLEAN) /\ (sfStep \in BOOLEAN) /\ (simStep \in BOOLEAN)

\* Specification: because this is a configuration module, the full spec
\* is just the spin on the backends and steps (always true here).
SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == TRUE

PROPERTIES ==
    /\ \A X \in {1, 2, 3}, Y \in {1, 2, 3} : (X \in Y) <=> (X = Y)
    /\ \A x \in {1, 2, 3} : \A y \in {1, 2, 3} : x \in y
====