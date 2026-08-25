---- MODULE TLAPS ----
EXTENDS FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T
  BY Zenon

THEOREM NoUniversalSet ==
  \A S : ~(\A x : x \in S)
  BY Z3
====