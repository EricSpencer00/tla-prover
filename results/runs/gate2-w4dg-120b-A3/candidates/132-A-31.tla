---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* The Boyer-Moore majority vote algorithm instantiated for model checking.
\* This module supplies the concrete constants and the bounded sequence
\* operator that the reference configuration expects.

CONSTANTS A, B, C, bound

\* Inherited from the main majority vote spec: Sequence, Position, Candidate,
\* Counter, Spec, Init, Next, TypeOK, Correct, Inv, Terminates.
\* The config rewrites Seq to BoundedSeq, so BoundedSeq must exist and Seq must
\* not be redefined here; EXTENDS Sequences stays in force.
BoundedSeq == [1..bound -> {A, B, C}]

\* Spec: scan the sequence fully, with the Boyer-Moore three-case logic.
Spec == Init /\ [][Next]_<<Candidate, Position, Counter, Sequence>>

INVARIANTS TypeOK, Correct, Inv
====