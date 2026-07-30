---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* Three model values are the payload of sequences; bound caps the length. Seq is
\* the bounded sequence constructor: all functions from 1..n to the value set,
\* for n ranging from zero up to bound.

Values == {A, B, C}

\* Scan position; candidate; counter. These are the main spec's variables.
VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
  /\ \E s \in Seq : seq = s
  /\ pos \in 1..5
  /\ cand \in Values
  /\ cnt = 0

\* The three-case majority-scan logic: adopt a new candidate, increment, or
\* decrement the counter.
Next ==
  \/ /\ pos <= 5
     /\ LET x == seq[pos] IN
        IF cnt = 0 THEN cand' = x /\ cnt' = 1
        ELSE IF x = cand THEN cnt' = cnt + 1
        ELSE cnt' = cnt - 1
     /\ pos' = pos + 1
  \/ (\A x \in {seq, pos, cand, cnt} : x' = x)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(\E x \in {seq, pos, cand, cnt} : x' = x)

TypeOK == /\ seq \in Seq
          /\ pos \in 1..5
          /\ cand \in Values
          /\ cnt \in Nat

\* Any true majority element of the input must equal the candidate after a
\* complete scan.
Correct == (cnt > 0 /\ \A i \in 1..5 : seq[i] = cand) => cand = seq[pos - 1]

Inv == /\ pos <= 5
       /\ IF cnt = 0 THEN TRUE
          ELSE \A i \in 1..5 : seq[i] = cand

====