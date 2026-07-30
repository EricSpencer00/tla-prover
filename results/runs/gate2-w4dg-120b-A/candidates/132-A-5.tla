---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* A bounded set of sequences (functions from 1..n to Values) with n up to
\* the model-bound; this is what keeps the model finite.
Seqs == {s \in [1..bound -> Values] : TRUE}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

\* The candidate may be any model value, not a user value; it is recorded as
\* the result of a nondeterministic choice on the previous count.
TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

\* The three cases of the Boyer-Moore scan: adopt a new candidate, increment
\* the counter, or decrement on a mismatch.
Next ==
  \/ /\ pos <= bound
     /\ LET x == seq[pos] IN
        IF count = 0 THEN /\ cand' = x
                           /\ count' = 1
        ELSE IF cand = x THEN /\ count' = count + 1
        ELSE /\ count' = count - 1
           /\ UNCHANGED cand
     /\ pos' = pos + 1
     /\ UNCHANGED seq
  \/ /\ pos > bound
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Any true majority of the input sequence must equal the surviving candidate.
Correct ==
  \A x \in Values :
    (2 * Cardinality({i \in DOMAIN seq : seq[i] = x}) > Cardinality(DOMAIN seq))
      => x = cand

\* The inductive invariant: the counter never exceeds the scan position.
Inv == count <= pos

\* The scan is guaranteed to reach the end of the sequence.
Complete == <>(pos > bound)
====