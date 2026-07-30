---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS). The
\* operators TLSZenon, TLSIsabel, TLSCVC3, TLSYices, TLSVeriT, TLSZ3, TLSSPASS,
\* and TLSLS4 name the automated provers that TLAPS may invoke for a given proof
\* obligation. The module also states two fundamental proof rules for set
\* theory: set extensionality and the fact that no set contains every value.
\* The `additional_assumptions` section reserves the names of some temporal
\* logic proof rules from Lamport's paper, preventing naming clashes.
\* The CONFIG file has no required identifiers for this module.

NoConsts == INTEGER

CONSTANTS
  TLSZenon, TLSIsabel, TLSCVC3, TLSYices,
  TLSVeriT, TLSZ3, TLSSPASS, TLSLS4

SPECIFICATION ==
  /\ TLSZenon = NoConsts
  /\ TLSIsabel = NoConsts
  /\ TLSCVC3 = NoConsts
  /\ TLSYices = NoConsts
  /\ TLSVeriT = NoConsts
  /\ TLSZ3 = NoConsts
  /\ TLSSPASS = NoConsts
  /\ TLSLS4 = NoConsts
  /\ Init == NoConsts
  /\ Next == NoConsts
  /\ InvarianceRule == NoConsts
  /\ WfRule == NoConsts
  /\ StepSimulationRule == NoConsts
  /\ SetExtensionality == NoConsts
  /\ NoSetContainsEveryValue == NoConsts

INIT == Init

NEXT == Next

INVARIANTS == {InvarianceRule, SetExtensionality, NoSetContainsEveryValue}

PROPERTIES == {WfRule, StepSimulationRule}

\* The following are placeholders: these proof rules are included for name
\* reservation only and have no operational effect here.
InvarianceRule == TRUE
WfRule == TRUE
StepSimulationRule == TRUE
SetExtensionality == TRUE
NoSetContainsEveryValue == TRUE

====