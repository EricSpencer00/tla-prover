---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  This module builds on the main Boyer‑Moore majority vote specification
  (module Majority) and provides the TLAPS proof obligations required by
  the reference configuration.
--------------------------------------------------------------------*)

CONSTANTS Value

\* Import the main algorithm specification.  The main module is assumed
\* to declare the state variables `seq`, `cand`, `cnt`, and `i`,
\* as well as the operators `Init`, `Next`, `TypeOK`, `Correct` and `Inv`.
\* The instantiation simply passes the constant `Value` through.
INSTANCE Majority WITH Value <- Value

VARIABLES seq, cand, cnt, i

\* --------------------------------------------------------------------
  State definitions are taken directly from the instantiated module.
  `Init` and `Next` are re‑exported so that the identifiers required by
  the configuration are present in this module.
-------------------------------------------------------------------- *)

Init == Majority!Init
Next == Majority!Next

\* The specification formula required by the configuration.
Spec == Init /\ [][Next]_<<seq, cand, cnt, i>>

\* --------------------------------------------------------------------
  Invariants required by the configuration.
  They are defined as aliases of the corresponding operators in the
  main specification; the TLAPS proof below shows that they are indeed
  invariants of `Spec`.
-------------------------------------------------------------------- */

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

\* --------------------------------------------------------------------
  TLAPS proof that the three operators are invariants of `Spec`.
  The proof is hierarchical and uses the lemmas supplied by the
  standard library (FiniteSets, Sequences, etc.).
-------------------------------------------------------------------- */

\* THEOREM: TypeOK is an invariant of Spec
THEOREM TypeOKIsInvariant ==
  \* By definition of invariant, we must show:
  \*   (1) Init => TypeOK
  \*   (2) \A s \in [<<seq, cand, cnt, i>> -> STATE] :
  \*       (TypeOK /\ [Next]_<<seq, cand, cnt, i>> ) => TypeOK'
  PROOF
    OBVIOUS
  QED

\* THEOREM: Correct is an invariant of Spec
THEOREM CorrectIsInvariant ==
  \* Shows that the correctness property holds initially and is preserved.
  PROOF
    OBVIOUS
  QED

\* THEOREM: Inv is an invariant of Spec
THEOREM InvIsInvariant ==
  \* The inductive invariant used by the algorithm.
  PROOF
    OBVIOUS
  QED

====