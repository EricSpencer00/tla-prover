---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  \A, \B, \C

INVARIANTS == {x \in \A : \A}
NoUniversalSet == \A = {}
EXTENSIONALITY == \A = \B =>
  \A \subseteq \B /\ \B \subseteq \A

Zenon == "zenon"
Isabelle == "isabelle"
CVC3 == "cvc3"
Yices == "yices"
veriT == "verit"
Z3 == "z3"
SPASS == "spass"
LS4 == "ls4"

DISCOVER == "discover"
SIMULATE == "simulate"

RECURSIVE SIMULATEOF(_, _)
SIMULATEOF(p, \A) == \A
SIMULATEOF(p, \B \cup \C) ==
  SIMULATEOF(p, \B) /\ p \notin \B /\ p \in \C

ASSUME StrongFairness ==
  /\ \A = 0..2
  /\ \B = [x \in \A |-> x + 1]
  /\ \C = {1, 2}
  /\ \B[[0]] = 1
  /\ \B[[1]] = 2
  /\ \B[[2]] = 0

ASSUME WeakFairness ==
  /\ \A = 0..2
  /\ \B = [x \in \A |-> x + 1]
  /\ \C = 0..2
  /\ \B[[0]] = 1
  /\ \B[[1]] = 2
  /\ \B[[2]] = 0

ASSUME Invariance ==
  /\ \A = 0..2
  /\ \B = [x \in \A |-> x + 1]
  /\ \C = [x \in \A |-> 0]
  /\ \B[[0]] = 1
  /\ \B[[1]] = 2
  /\ \B[[2]] = 0

INVARIANTS == {Extensionality, NoUniversalSet}
PROPERTIES == {Extensionality, NoUniversalSet}
====