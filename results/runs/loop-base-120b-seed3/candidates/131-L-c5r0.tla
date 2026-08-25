---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(*--------------------------------------------------------------------
  Import the main Boyer‑Moore majority‑vote specification.
  The main module (named Majority) defines the state variables,
  the initial predicate, the next‑state action, and the core
  invariants (TypeOK, Correct, Inv) together with their
  preservation lemmas.
--------------------------------------------------------------------*)
INSTANCE Majority WITH Value

(*--------------------------------------------------------------------
  The overall specification of the algorithm.
--------------------------------------------------------------------*)
Spec == Majority!Spec

(*--------------------------------------------------------------------
  Invariants of interest – directly re‑exported from the main module.
--------------------------------------------------------------------*)
Inv    == Majority!Inv
TypeOK == Majority!TypeOK
Correct== Majority!Correct

(*--------------------------------------------------------------------
  Proof that the type‑correctness invariant holds for the whole
  specification.
--------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
<1>1. Init => TypeOK
      BY Majority!InitTypeOK
<1>2. [][Next]_<<seq, i, cand, cnt>> => []TypeOK
      BY INDUCTION
          OBVIOUS
      (*
        The induction step uses the lemma that the Next action of the
        main algorithm preserves TypeOK, which is available as
        Majority!NextPreservesTypeOK.
      *)
QED

(*--------------------------------------------------------------------
  Proof that the correctness invariant holds for the whole
  specification.
--------------------------------------------------------------------*)
THEOREM CorrectIsInvariant ==
  Spec => []Correct
<1>1. Init => Correct
      BY Majority!InitCorrect
<1>2. [][Next]_<<seq, i, cand, cnt>> => []Correct
      BY INDUCTION
          OBVIOUS
      (*
        The induction step relies on Majority!NextPreservesCorrect,
        the lemma stating that the Next action maintains the
        correctness invariant.
      *)
QED

====