---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon
CONSTANTS Isabelle
CONSTANTS CVC3
CONSTANTS Yices
CONSTANTS VeriT
CONSTANTS Z3
CONSTANTS SPASS
CONSTANTS LS4

NoProof == -1

Dispatch == [pmt : {"Zenon", "Isabelle", "CVC3", "Yices", "VeriT", "Z3", "SPASS", "LS4"},
              timeout : 1..3,
              tactic : {"default", "none"}]

Spec == "full"
InitHint == "default"
NextHint == "default"

SPECIFICATION == "fast"
INIT == "fast"
NEXT == "fast"
INVARIANTS == "fast"
PROPERTIES == "fast"

SetExtensionality == \A x \in {y \in {1, 2} : TRUE} : \A y \in {y \in {1, 2} : TRUE} : (x = y) => (x \in {y \in {1, 2} : TRUE} <=> y \in {y \in {1, 2} : TRUE})
NoSetContainsAll == \A x \in {y \in {1, 2} : TRUE} : \A y \in {y \in {1, 2} : TRUE} : ~(x \in y)

====