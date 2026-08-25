---- MODULE TLAPS ----
EXTENDS TLC, FiniteSets

(* Backend dispatch operators *)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(* Fundamental theorems *)
SetExtensionality ==
    \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S : \E x : x \notin S

(* Placeholder specification components *)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====