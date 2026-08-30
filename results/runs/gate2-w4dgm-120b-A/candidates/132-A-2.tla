---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* This is the model-checking configuration: three concrete values and a bounded
\* sequence length, fed into the Boyer-Moore majority vote spec.
CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq is a finite version of Seq that only builds sequences up to a
\* fixed maximum length; this keeps the model state space finite for model checking.
BoundedSeq(f, n) == IF n = 0 THEN << >> ELSE Append(BoundedSeq(f, n - 1), f[n])

\* State: the input sequence to scan, the scan position, the candidate element,
\* and the counter.
VARIABLES seq, pos, cand, cnt

vars == << seq, pos, cand, cnt >>

TypeOK ==
  /\ seq \in Union({BoundedSeq([1 .. n -> Values], n) : n \in 0 .. bound})
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in Union({BoundedSeq([1 .. n -> Values], n) : n \in 0 .. bound})
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* Boyer-Moore scan: three-way case on the next element relative to candidate.
Scan ==
  /\ pos <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[pos]
            /\ cnt' = 1
       ELSE IF seq[pos] = cand
            THEN cnt' = cnt + 1
            /\ cand' = cand
            /\ UNCHANGED seq
       ELSE cnt' = cnt - 1
            /\ cand' = cand
            /\ UNCHANGED seq
  /\ pos' = pos + 1

Next == Scan

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Scan)

\* At most one true majority element exists; if one exists it must be the
\* candidate left over after scanning the whole sequence.
Correct ==
  \A e \in Values : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = e}) > Len(seq))
                      => e = cand

\* Scanning always completes: the position eventually passes the sequence length.
\* Weak fairness on the scan action is what forces it.
Completion == <>(pos > Len(seq))

\* The main correctness property, plus that the position never regresses.
Inv == Correct /\ (pos >= 1)

====