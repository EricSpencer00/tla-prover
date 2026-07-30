---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Backends,
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  VeriT,
  Z3,
  SPASS,
  LS4,
  Timeout,
  ParaLimit,
  SimSteps,
  Syntactic

Zero == 0

VARIABLES
  invariance,
  wellformed,
  strongfair,
  weakfair,
  stepsim

vars == <<invariance, wellformed, strongfair, weakfair, stepsim>>

TYPEDEF == invariance \in BOOLEAN /\ wellformed \in BOOLEAN
          /\ strongfair \in BOOLEAN /\ weakfair \in BOOLEAN /\ stepsim \in BOOLEAN

Init ==
  /\ invariance = FALSE
  /\ wellformed = FALSE
  /\ strongfair = FALSE
  /\ weakfair = FALSE
  /\ stepsim = FALSE

Invoke(l) ==
  /\ l \in Backends
  /\ stepsim' = TRUE
  /\ UNCHANGED <<invariance, wellformed, strongfair, weakfair>>

ApplyInvariance ==
  /\ ~invariance
  /\ invariance' = TRUE
  /\ UNCHANGED <<wellformed, strongfair, weakfair, stepsim>>

ApplyWellFormedness ==
  /\ ~wellformed
  /\ wellformed' = TRUE
  /\ UNCHANGED <<invariance, strongfair, weakfair, stepsim>>

ApplyStrongFair ==
  /\ ~strongfair
  /\ strongfair' = TRUE
  /\ UNCHANGED <<invariance, wellformed, weakfair, stepsim>>

ApplyWeakFair ==
  /\ ~weakfair
  /\ weakfair' = TRUE
  /\ UNCHANGED <<invariance, wellformed, strongfair, stepsim>>

StepSimulation ==
  /\ ~stepsim
  /\ stepsim' = TRUE
  /\ UNCHANGED <<invariance, wellformed, strongfair, weakfair>>

Next ==
  \/ \E l \in Backends : Invoke(l)
  \/ ApplyInvariance
  \/ ApplyWellFormedness
  \/ ApplyStrongFair
  \/ ApplyWeakFair
  \/ StepSimulation

Spec == Init /\ [][Next]_vars

TemporalInvariance == invariance

TemporalWellFormedness == wellformed

StrongFairness == strongfair

WeakFairness == weakfair

StepSimulation == stepsim

Extensionality ==
  \A X \in {0, 1}, Y \in {0, 1} :
    (\A e \in {0, 1} : (e \in X) <=> (e \in Y)) => (X = Y)

NoUniversalSet ==
  \A X \in {0, 1} : X # 1

====