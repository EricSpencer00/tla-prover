---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  \A, \B, \C, \D, \E, \F, \G, \H, \I, \J, \K, \L, \M, \N, \O, \P, \Q, \R,
  \S, \T, \U, \V, \W, \X, \Y, \Z

ASSUME
  /\ \A = "A"
  /\ \B = "B"
  /\ \C = "C"
  /\ \D = "D"
  /\ \E = "E"
  /\ \F = "F"
  /\ \G = "G"
  /\ \H = "H"
  /\ \I = "I"
  /\ \J = "J"
  /\ \K = "K"
  /\ \L = "L"
  /\ \M = "M"
  /\ \N = "N"
  /\ \O = "O"
  /\ \P = "P"
  /\ \Q = "Q"
  /\ \R = "R"
  /\ \S = "S"
  /\ \T = "T"
  /\ \U = "U"
  /\ \V = "V"
  /\ \W = "W"
  /\ \X = "X"
  /\ \Y = "Y"
  /\ \Z = "Z"

\* This module provides no state and no actions: it declares the set- and
\* prover-backend constants that TLAPS consults when compiling a proof, and
\* it declares the foundational theorems that the standard library already
\* contains as unproved facts.

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

INVARIANTS ==
  /\ \A \cup \B = \B \cup \A
  /\ ~(TRUE)  \* Every set is proper: none contains every possible value.

PROPERTIES == INVARIANTS

====