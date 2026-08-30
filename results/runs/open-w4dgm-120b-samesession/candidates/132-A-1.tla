---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* BoundedSeq is the finite version of Seq that the model-checking configuration
\* replaces for Seq with; it keeps the state space finite while preserving semantics.
BoundedSeq == [n \in 0..bound |-> [i \in 1..n |-> IF i \in 1..n THEN CHOOSE v \in {A, B, C} : TRUE ELSE A]]

CONSTANTS A, B, C, bound

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

SeqDom == 1..Len(seq)

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in SeqDom \cup {0}
  /\ cand \in {A, B, C}
  /\ cnt \in 0..3

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

\* The Boyer-Moore scan logic: adopt a new candidate, increment, or decrement.
Next ==
  /\ pos <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[pos]
            /\ cnt' = 1
            /\ pos' = pos + 1
            /\ UNCHANGED seq
       ELSE IF seq[pos] = cand
            THEN /\ cnt' = cnt + 1
                 /\ pos' = pos + 1
                 /\ UNCHANGED <<seq, cand>>
            ELSE /\ cnt' = cnt - 1
                 /\ pos' = pos + 1
                 /\ UNCHANGED <<seq, cand>>

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

\* If a true majority exists it must be the candidate at the end of the scan.
Correct == (\E x \in {A, B, C} : 2 * Cardinality({i \in SeqDom : seq[i] = x}) > Len(seq))
              => cand = (CHOOSE x \in {A, B, C} :
                           2 * Cardinality({i \in SeqDom : seq[i] = x}) > Len(seq})

Inv == (pos = Len(seq) + 1) => (cnt >= 1 \/ \A x \in {A, B, C} : 2 * Cardinality({i \in SeqDom : seq[i] = x}) <= Len(seq))

====