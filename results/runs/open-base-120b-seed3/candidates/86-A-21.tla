---- MODULE TLAPS ----
EXTENDS Naturals, TLC

(* ----------------------------------------------------------------------
   Backend prover placeholders (no operational effect, only names reserved)
   ---------------------------------------------------------------------- *)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(* ----------------------------------------------------------------------
   Fundamental theorems required by the description
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
    \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
    \A S : \E x : x \notin S

(* ----------------------------------------------------------------------
   Skeleton of a TLA+ specification (required identifiers)
   ---------------------------------------------------------------------- *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====