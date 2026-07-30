---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
    NoOp

ASSUME NoOp \in BOOLEAN

ASSUME SET_EXTENSIVITY ==
  \A S \in SUBSET Nat, T \in SUBSET Nat :
    (\A x \in Nat : (x \in S) <=> (x \in T)) => (S = T)

ASSUME NO_SET_CONTAINS_ALL_VALUES ==
  \A S \in SUBSET Nat :
    (\A x \in Nat : x \in S) => (Nat = {})

ASSUME Zenon == NoOp
ASSUME Isabelle == NoOp
ASSUME CVC3 == NoOp
ASSUME Yices == NoOp
ASSUME veriT == NoOp
ASSUME Z3 == NoOp
ASSUME SPASS == NoOp
ASSUME LS4 == NoOp

ASSUME INV ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) => (Nat = {})

ASSUME WF1 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME SF1 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME WF2 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME WF3 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME SF2 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME SF3 ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

ASSUME STEP ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) ~> (Nat = {})

Spec == TRUE

Init == TRUE

Next == TRUE

Invariants == TRUE

Properties == TRUE

====