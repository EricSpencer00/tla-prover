---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Backends

ASSUME Backends \in { "zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4" }

SpecOp == "zenon"
ProofOp == "isabelle"
SMTOp == "z3"
Timeout == 5
Tactic == "default"

SPECIFICATION == SpecOp
INIT == ProofOp
NEXT == SMTOp
INVARIANTS == { "setExtensionality", "noSetContainsAllValues" }
PROPERTIES == { "setExtensionality", "noSetContainsAllValues" }

setExtensionality == \A X \in SUBSET <<>>, Y \in SUBSET <<>> :
                     (\A e \in <<>> : e \in X <=> e \in Y) => X = Y

noSetContainsAllValues == \A X \in SUBSET <<>> : \A v \in <<>> : v \notin X

====