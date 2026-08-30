---- MODULE TLAPS ----
EXTENDS Naturals
CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4
ASSUME Zenon = "Zenon" /\ Isabelle = "Isabelle" /\ CVC3 = "CVC3"
  /\ Yices = "Yices" /\ VeriT = "VeriT" /\ Z3 = "Z3" /\ SPASS = "SPASS"
  /\ LS4 = "LS4"
Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == TRUE
Properties == TRUE
====