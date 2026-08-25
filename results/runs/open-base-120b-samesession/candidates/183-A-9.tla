---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Backend prover pragmas – these are defined as identity operators
  so that TLAPS can recognise the names when used as annotations.
-----------------------------------------------------------------*)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule placeholders.
  Their bodies are trivial; they exist only to reserve the names.
-----------------------------------------------------------------*)
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(*-----------------------------------------------------------------
  Minimal behavioural skeleton (required by the task).
-----------------------------------------------------------------*)
VARIABLES vars

Init == TRUE

Next == UNCHANGED vars

SPECIFICATION == Init /\ [] [Next]_vars

INIT == Init
NEXT == Next
INVARIANTS == <<>>            \* empty tuple of invariants
PROPERTIES == <<>>            \* empty tuple of properties

(*-----------------------------------------------------------------
  Fundamental theorems required by the description.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

====