---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers/solvers that TLAPS may dispatch to.  These ops are         *)
(* configuration primitives for the prover, not steps of a concurrent       *)
(* system -- there are no actors and no shared state to guard.              *)
\* The standard TLA+ library already defines an operator \E for existential  *)
(* quantification; to keep the reserved-name bookkeeping honest, the membership *)
(* primitive \in is defined here as well and is deliberately left out of the  *)
(* exported set.                                                              *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Primitive form.  The semantics is set membership: x \in S means S is a set
\* and x is one of its elements.  The library already exports quantifier \E,
\* so the identifier \in stays reserved but unexported here.
\in == \E x \in S : x \in S

(* Basic set-theoretic facts that the prover can always appeal to. *)
SetExtensionality ==
    \A S, T \in SUBSET Nat :
        (\A x \in Nat : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    \A S \in SUBSET Nat : (\A x \in Nat : x \in S) => S # {}

(* Backends: each operator names the prover that should take the next      *)
(* proof obligation, together with any fixed timeout or tactic.           *)
ZenonOp == Zenon
IsabelleOp == Isabelle
CVC3Op == CVC3
YicesOp == Yices
VeriTOp == VeriT
Z3Op == Z3
SPASSOp == SPASS
LS4Op == LS4

(* A TLA+ system spec must expose SPEC/INIT/NEXT/INVARIANTS/PROPERTIES.   *)
SPEC == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {SetExtensionality, NoUniversalSet}
PROPERTIES == {}

====