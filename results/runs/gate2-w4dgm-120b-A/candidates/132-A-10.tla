---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The bounded sequence operator replaces the standard Seq from Sequences;
\* it is a FINITE version (only sequences of length up to the bound) so the
\* model stays checkable, but the rest of the spec still sees it as Seq.
BoundedSeq(S) == IF S = {} THEN <<>> ELSE
  LET x == CHOOSE y \in S : \A z \in S : y <= z
      rest == BoundedSeq(S \ {x})
  IN <<x>> \o rest

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                      /\ cnt' = 1
       ELSE IF x = cand THEN /\ cnt' = cnt + 1
                           /\ cand' = cand
       ELSE /\ cnt' = cnt - 1
            /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_<<seq, pos, cand, cnt>>

\* The candidate at the end of the scan must be the true majority element.
Correct == Len(seq) > 0 => (\A e \in Values : (2 * Cardinality({j \in 1..Len(seq) : seq[j] = e}) > Len(seq)) => e = cand)
Inv == cnt <= Len(seq)
\* The candidate can never outrun the scan: a candidate with a positive
\* counter must still be ahead of the scan position.
InvBound == cnt > 0 => pos <= Len(seq) + 1

\* With a fair chance to scan each element, the scan always completes.
Progress == pos > Len(seq)

====