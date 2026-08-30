---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

(* Model-checking configuration for the Boyer-Moore majority vote algorithm.    *)
(* Concrete values are A, B, C with a bounded sequence length (the bound is      *)
(* configured in the .cfg).  All operators below are exactly the ones the       *)
(* reference configuration expects; none may be renamed or omitted.              *)

CONSTANTS A, B, C, bound

\* The three-element value set used to generate bounded sequences.
Values == {A, B, C}

\* A bounded version of the standard Seq operator from the Sequences module,  *)
(* kept finite so the model state space stays finite for model checking.      *)
BoundedSeq(S) == CHOOSE seq \in [1..Cardinality(S) -> Values] :
                    \A x \in S : \E i \in 1..Cardinality(S) : seq[i] = x

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

\* A sequence of bounded length chosen nondeterministically from all sequences
\* over the three-element set up to that length, plus a nondeterministic start
\* candidate for the Boyer-Moore scan.
InitConst == CHOOSE s \in UNION { [1..n -> Values] : n \in 0..bound } : TRUE

TypeOK ==
    /\ seq \in UNION { [1..n -> Values] : n \in 0..bound }
    /\ pos \in 1..(bound + 1)
    /\ cand \in {A, B, C}
    /\ cnt \in 0..bound

\* Boyer-Moore scan: compare the next element with the current candidate.
Step ==
    \/ \E e \in Values :
        /\ pos <= Len(seq)
        /\ (IF e = cand
              THEN /\ cand' = cand
                   /\ cnt' = cnt + 1
              ELSE IF cnt = 0
                   THEN /\ cand' = e
                        /\ cnt' = 1
                   ELSE /\ cand' = cand
                        /\ cnt' = cnt - 1)
        /\ pos' = pos + 1
        /\ seq' = seq
    \/ (pos <= Len(seq) /\ pos' = pos + 1)
    /\ UNCHANGED <<seq, cand, cnt>>

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Init == InitConst /\ pos = 1 /\ cnt = 0

\* The majority vote is a strict majority of the scanned elements.
Majority == Cardinality({ i \in 1..Len(seq) : seq[i] = cand }) * 2 > Len(seq)

\* Correctness: a true majority element must be the surviving Boyer-Moore
\* candidate after the entire scan has completed.
Correct == (Majority => (cand = seq[1]))

\* Intended inductive invariant: candidate dominance over the scanned prefix.
\* Not meant to hold on the whole sequence, so it cannot be used alone to
\* prove Majority; it is kept as a sanity check on the scan's shape.
Inv == \A i \in 1..(pos - 1) : seq[i] = cand

MajorityImpliesCandidate == Majority => cand = seq[1]

\* Completion of the scan: the pointer reaches the end of the sequence.
Complete == pos = Len(seq) + 1

CompleteScan == TRUE [][Step]_vars /\ WF_vars(Step)

====