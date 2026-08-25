---- MODULE TLAPS ----
EXTENDS TLC

(*-----------------------------------------------------------------
  Backend dispatch operators for TLAPS.
  These operators are identity functions whose purpose is to
  carry TLAPS pragmas indicating which backend prover should be
  used for the enclosed proof obligation.
-----------------------------------------------------------------*)

Zenon(p) == p
(*- ZENON -*)

Isabelle(p) == p
(*- ISABELLE -*)

CVC3(p) == p
(*- CVC3 -*)

Yices(p) == p
(*- YICES -*)

VeriT(p) == p
(*- VERIT -*)

Z3(p) == p
(*- Z3 -*)

SPASS(p) == p
(*- SPASS -*)

LS4(p) == p
(*- LS4 -*)

(*-----------------------------------------------------------------
  Fundamental theorems
-----------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====