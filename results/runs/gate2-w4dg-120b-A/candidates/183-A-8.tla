---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  none

SPECIFICATION == "The set of backend provers for TLAPS: Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4."
INIT == "No backend action is defined, since this module configures provers rather than models a process."
NEXT == "No next-state action is defined, since this module configures provers rather than models a process."
INVARIANTS == "Set extensionality: any two sets with the same elements are equal."
PROPERTIES == "No set contains every possible value, which keeps the universe properly bounded."
====