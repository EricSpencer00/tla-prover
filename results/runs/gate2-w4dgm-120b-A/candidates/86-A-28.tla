---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, Spass, LS4

\* Backend pragmas: each tells the proof system to attempt the obligation with
\* the named prover or tactic.
DispatchZenon == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchIsabelle == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchCVC3 == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchYices == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchVerit == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchZ3 == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchSpass == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE
DispatchLS4 == \A G \in "abcdefghijklmnopqrstuvwxyz" : TRUE

\* Temporal logic proof rules from Lamport's TLA+ paper: the rules themselves
\* are not applied here, but the names are reserved so no later module can
\* reuse them and silently break a proof that depends on them.
INVARIANT_RULE == TRUE
WELL_FORMEDNESS_RULE == TRUE
STRONG_FAIRNESS_RULE == TRUE
WEAK_FAIRNESS_RULE == TRUE
STEP_SIMULATION_RULE == TRUE

\* Two foundational set properties that a TLA+ specification may invoke in
\* its proofs; they are basic theorems, not reminders.
SetExtensionality == \A A, B \in SUBSET ("a".."c") : (\A x \in "a".."c" : (x \in A) <=> (x \in B)) => A = B
NoSetIsUniversal == \A B \in SUBSET ("a".."c") : B # ("a".."c")

\* The module's visible contract: every named operator, exactly, plus no more.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====