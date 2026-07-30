---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A bounded version of Seq: only functions from 1..n with n <= bound.
BoundedSeq(T) == UNION { [1..n -> T] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* Scan the next element, applying the Boyer-Moore three-way rule.
Next ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0
         THEN /\ cand' = x
              /\ cnt' = 1
         ELSE IF x = cand
              THEN /\ cnt' = cnt + 1
              /\ UNCHANGED cand
              ELSE /\ cnt' = cnt - 1
                   /\ UNCHANGED cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars
            /\ WF_vars(Next)

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

\* After a complete scan, any majority element must match the candidate.
Correct ==
  (cnt > 0 /\ 2 * Cardinality({ i \in 1..Len(seq) : seq[i] = cand }) > Len(seq))
    => (cand \in Values)

\* The main invariant of the Boyer-Moore algorithm.
Inv ==
  (cnt > 0) => (cand \in Values)

Completion == pos > Len(seq)

====