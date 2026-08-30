---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Pragmas == "Pragmas"
Init == "Init"
InvRule == "InvRule"
WfRule == "WfRule"
SFRule == "SFRule"
WFRule == "WFRule"
SimStep == "SimStep"
EXT == "EXT"
NoUniversal == "NoUniversal"

Specification == Zenon /\ Isabelle /\ CVC3 /\ Yices /\ VeriT /\ Z3 /\ SPASS /\ LS4
Init == Pragmas
InvRule == Pragmas
WfRule == Pragmas
SFRule == Pragmas
WFRule == Pragmas
SimStep == Pragmas
EXT == EXT
NoUniversal == NoUniversal

Spec == Specification
InitState == Init
NextStep == InvRule
StateInv == WfRule
TemporalProps == SFRule
AdditionalProps == WFRule

SetExtensionality == EXT
NoSetUniversal == NoUniversal
====