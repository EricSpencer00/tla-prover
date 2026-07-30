---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon
  ZenonStep
  Isabelle
  CVC3
  Yices
  VeriT
  Z3
  Spass
  LS4
  Liveness
  Safety
  Extensionality
  NoSetIsUniversal

VARIABLES
  lastUsed

vars == <<lastUsed>>

TypeOK ==
  /\ lastUsed \in {"none", "Zenon", "Isabelle", "CVC3", "Yices", "VeriT", "Z3", "Spass", "LS4"}

Init ==
  /\ lastUsed = "none"

SetExtensionality ==
  \A x \in {1, 2, 3}, y \in {1, 2, 3} : (x = y) => (x \in y)

NoSetIsUniversal ==
  \A x \in {1, 2, 3} : ~ (x \in {1, 2, 3})

ZenonTimeout == 0

DispatchZenon ==
  /\ ZenonTimeout > 0
  /\ lastUsed' = "Zenon"
  /\ UNCHANGED vars

DispatchIsabelle ==
  /\ lastUsed' = "Isabelle"
  /\ UNCHANGED vars

DispatchCVC3 ==
  /\ lastUsed' = "CVC3"
  /\ UNCHANGED vars

DispatchYices ==
  /\ lastUsed' = "Yices"
  /\ UNCHANGED vars

DispatchVeriT ==
  /\ lastUsed' = "VeriT"
  /\ UNCHANGED vars

DispatchZ3 ==
  /\ lastUsed' = "Z3"
  /\ UNCHANGED vars

DispatchSpass ==
  /\ lastUsed' = "Spass"
  /\ UNCHANGED vars

DispatchLS4 ==
  /\ lastUsed' = "LS4"
  /\ UNCHANGED vars

Next ==
  \/ DispatchZenon
  \/ DispatchIsabelle
  \/ DispatchCVC3
  \/ DispatchYices
  \/ DispatchVeriT
  \/ DispatchZ3
  \/ DispatchSpass
  \/ DispatchLS4
  \/ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars

Init ==
  /\ lastUsed = "none"
  /\ UNCHANGED vars

InvarianceRule ==
  \E x \in {1, 2, 3} :
    /\ Liveness
    /\ x

WellFormednessRule ==
  \E x \in {1, 2, 3} :
    /\ x
    /\ Safety

StrongFairnessRule ==
  \E x \in {1, 2, 3} :
    /\ Liveness
    /\ x

WeakFairnessRule ==
  \E x \in {1, 2, 3} :
    /\ \A y \in {1, 2, 3} : y
    /\ x

StepSimulationRule ==
  \E x \in {1, 2, 3} :
    /\ \A y \in {1, 2, 3} : y
    /\ x

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A x \in {1, 2, 3} : x

Properties == SetExtensionality /\ NoSetIsUniversal

====