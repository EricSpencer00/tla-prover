---- MODULE TLAPS ----
EXTENDS TLC, FiniteSets

(* ---------------------------------------------------------------------- *)
(* Backend provers for TLAPS.  These operators are used as annotations in *)
(* proofs; they simply return their argument unchanged.                    *)
(* ---------------------------------------------------------------------- *)

Zenon(p)    == p
Isabelle(p) == p
CVC3(p)    == p
Yices(p)   == p
VeriT(p)   == p
Z3(p)      == p
SPASS(p)   == p
LS4(p)     == p

(* ---------------------------------------------------------------------- *)
(* Fundamental theorems required by the description.                     *)
(* ---------------------------------------------------------------------- *)

THEOREM_SetExtensionality ==
    \A A, B \in SUBSET UNIV :
        (\A x : (x \in A) <=> (x \in B)) => A = B

THEOREM_NoUniversalSet ==
    \A S : ~ (UNIV \subseteq S)

(* ---------------------------------------------------------------------- *)
(* Trivial specification skeleton required by the task.                  *)
(* ---------------------------------------------------------------------- *)

INIT == TRUE

NEXT == TRUE

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}

PROPERTIES == {}

====