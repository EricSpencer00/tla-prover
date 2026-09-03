---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Atom, MaxSetSize

VARIABLES specStage, specCount

vars == <<specStage, specCount>>

TypeOK ==
  /\ specStage \in {"init", "running", "done"}
  /\ specCount \in 0..3

Init ==
  /\ specStage = "init"
  /\ specCount = 0

Begin ==
  /\ specStage = "init"
  /\ specStage' = "running"
  /\ UNCHANGED specCount

Complete ==
  /\ specStage = "running"
  /\ specStage' = "done"
  /\ UNCHANGED specCount

Recycle ==
  /\ specStage = "done"
  /\ specStage' = "init"
  /\ UNCHANGED specCount

SpecStep ==
  \/ Begin
  \/ Complete
  \/ Recycle

SpecNext == SpecStep

Specification == SpecStep

SpecStateBound == specCount <= 3

SpecStatusChanges == (specStage = "init") ~> (specStage = "done")

InitInv == specStage = "init"

StateInv == TRUE

SpecProps == TypeOK /\ SpecStateBound

Next == SpecStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SpecStep)

====