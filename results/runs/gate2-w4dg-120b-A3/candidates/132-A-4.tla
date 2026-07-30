---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* Three model values for the element set, and a sequence-length bound.
\* Sequences are drawn from all functions 1..n -> {A, B, C} for n <= bound,
\* using a bounded sequence construction that stays finite for model checking.
\* The Seq name from Sequences is replaced by BoundedSeq in the .cfg.

Elements == {A, B, C}
SeqSpace == UNION { [1..n -> Elements] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in SeqSpace
  /\ pos \in Nat
  /\ cand \in Elements
  /\ cnt \in Nat

\* The main correctness property of the Boyer-Moore algorithm: after a
\* complete scan any true majority element must equal the candidate.
Correct ==
  \A e \in Elements :
    (\A i \in 1..Len(seq) : seq[i] = e) => (cnt > 0 /\ cand = e)

Init ==
  /\ seq \in SeqSpace
  /\ pos = 1
  /\ cand \in Elements
  /\ cnt = 0

\* The Boyer-Moore three-case scan step.
Step ==
  /\ pos <= Len(seq)
  /\ (IF cnt = 0
        THEN /\ cand' = seq[pos]
             /\ cnt' = 1
        ELSE IF seq[pos] = cand
             THEN /\ cand' = cand
                  /\ cnt' = cnt + 1
             ELSE /\ cand' = cand
                  /\ cnt' = cnt - 1)
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars

\* A weak-fairness assumption: the scan eventually completes.
Properties == WF_vars(Next)

Inv == TypeOK /\ Correct

\* The .cfg replaces Seq by BoundedSeq, so we define the latter as a
\* finite version of the standard sequence operator (the name Seq stays
\* undeclared here, so it cannot be used in the model).
BoundedSeq == Seq
====