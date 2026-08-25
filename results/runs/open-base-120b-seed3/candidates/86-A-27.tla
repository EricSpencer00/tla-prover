---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

CONSTANT Universe

(* Assume the universe of discourse is non‑empty. *)
ASSUME Universe # {}

(* ---------------------------------------------------------------------- *)
(* Fundamental set theorems                                               *)
(* ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x \in Universe : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  ~\E S \in SUBSET Universe : \A x \in Universe : x \in S

(* ---------------------------------------------------------------------- *)
(* Specification skeleton (no state variables)                            *)
(* ---------------------------------------------------------------------- *)

INIT == TRUE

NEXT == TRUE

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}

PROPERTIES == {}

(* ---------------------------------------------------------------------- *)
(* Backend prover pragma placeholders (no operational effect)            *)
(* ---------------------------------------------------------------------- *)

Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
veriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

====