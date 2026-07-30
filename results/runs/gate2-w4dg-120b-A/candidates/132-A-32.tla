---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

\* Concrete element set derived from three model constants.
Values == {A, B, C}

\* Bounded sequences: all functions from 1..n to the value set, for n up to bound.
Seqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

\* Majority vote's scan actions (adopt, increment, decrement) are imported as
\* sub-actions of a single step to keep the spec flat.
\* Action: scan the next element with the three-case majority logic.
Step ==
  \/ \E x \in Values :
       /\ pos <= Len(seq)
       /\ pos' = pos + 1
       /\ IF cand = 0 THEN cand' = x
          ELSE IF cand = x THEN cand' = x
          ELSE cand' = cand
       /\ IF cand \in {0, x} THEN cnt' = cnt + 1
          ELSE cnt' = cnt - 1
       /\ UNCHANGED seq
  \/ (pos > Len(seq) /\ UNCHANGED vars)

Init ==
  \E w \in Seqs :
    /\ seq = w
    /\ pos = 1
    /\ cand \in Values \cup {0}
    /\ cnt = 0

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

TypeOK == seq \in Seqs /\ pos \in 1..(bound + 1)
          /\ cand \in Values \cup {0} /\ cnt \in 0..bound

\* Any true majority element must equal the candidate after a complete scan.
Correct == \A c \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = c}) > Len(seq)) => cand = c

Inv == cnt >= 0

====