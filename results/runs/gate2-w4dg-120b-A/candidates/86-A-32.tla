---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Z3Timeout, ZenonTimeout, YicesTimeout, CVC3Timeout, SPASSTimeout

SpecVersion == "TLAPS"
Backends == {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"}

\* Pragmas for each backend prover, naming the timeout it runs under.
ZapZenon == [kind |-> "dispatch", smt |-> "none", timeout |-> ZenonTimeout]
ZapIsabelle == [kind |-> "dispatch", smt |-> "none", timeout |-> Z3Timeout]
ZapCVC3 == [kind |-> "dispatch", smt |-> "cvc3", timeout |-> CVC3Timeout]
ZapYices == [kind |-> "dispatch", smt |-> "yices", timeout |-> YicesTimeout]
ZapVeriT == [kind |-> "dispatch", smt |-> "verit", timeout |-> 2]
ZapZ3 == [kind |-> "dispatch", smt |-> "z3", timeout |-> Z3Timeout]
ZapSPASS == [kind |-> "dispatch", smt |-> "none", timeout |-> SPASSTimeout]
ZapLS4 == [kind |-> "dispatch", smt |-> "none", timeout |-> 2]

\* Temporal logic proof rules from Lamport's TLA paper. They have no body here;
\* their role is to reserve the rule names and prevent future naming clashes.
TLAInvarianceRule == TRUE
TLAWellFormednessRule == TRUE
TLAStrongFairnessRule == TRUE
TLAWeakFairnessRule == TRUE
TLAStepSimulationRule == TRUE

SpecVersionOp == SpecVersion
SpecOp == "This module defines TLAPS backend pragmas and proof rules."
InitOp == TRUE
NextOp == TRUE

RECURSIVE EqualSets(_)
EqualSets(S) ==
  IF S = {} THEN TRUE
  ELSE \E a \in S : \A b \in S : a = b

NoSetContainsEveryValue == \A S \in (SUBSET Nat) : \E b \in S : TRUE

Spec == SpecVersionOp /\ SpecOp /\ InitOp /\ NextOp /\ EqualSets({}) /\ NoSetContainsEveryValue
====