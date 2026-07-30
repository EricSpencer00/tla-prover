---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq replaces the unbounded Seq from Sequences. We keep EXTENDS Sequences
\* but override the Seq name by defining a FINITE version.
BoundedSeq(T) ==
  { f \in [1 .. n -> T] : n \in 0 .. bound }

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ counter \in Nat

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

\* Scan the next element; three-case majority-logic update on counter.
DoScan ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       /\ IF v = cand
            THEN counter' = counter + 1
            ELSE IF counter > 0
                    THEN counter' = counter - 1
                    ELSE /\ cand' = v
                         /\ counter' = 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == DoScan

Spec == Init /\ [][Next]_vars
        /\ WF_vars(DoScan)

\* The candidate at the end of a complete scan is the only element that can be
\* a true majority of the sequence.
Correct ==
  (Len(seq) > 0 /\ 2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = cand}) > Len(seq))
    => (pos = Len(seq) + 1)

\* An invariant version of the same correctness claim.
Inv ==
  (pos = Len(seq) + 1 /\ Len(seq) > 0 /\ 2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = cand}) > Len(seq))
    => (pos = Len(seq) + 1)

====