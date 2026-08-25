---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS U

(*-----------------------------------------------------------------
  Backend prover dispatch operators (pragmas)
-----------------------------------------------------------------*)
Zenon(p) == @\z{Zenon} p
Isabelle(p) == @\z{Isabelle} p
CVC3(p) == @\z{CVC3} p
Yices(p) == @\z{Yices} p
VeriT(p) == @\z{VeriT} p
Z3(p) == @\z{Z3} p
SPASS(p) == @\z{SPASS} p
LS4(p) == @\z{LS4} p

(*-----------------------------------------------------------------
  Temporal‑logic proof rules (names reserved for future use)
-----------------------------------------------------------------*)
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET U :
    (\A x \in U : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S \in SUBSET U :
    ~(\A x \in U : x \in S)

(*-----------------------------------------------------------------
  Specification skeleton (no real state)
-----------------------------------------------------------------*)
VARIABLES dummy

Init == dummy = 0

Next == /\ dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====