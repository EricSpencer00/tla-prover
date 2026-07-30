---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A bounded version of the standard Seq operator: only sequences of length
\* up to the configured bound are in the state space.
BoundedSeq == {s \in Seq(Values) : Len(s) <= bound}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* The three-case scan step of the Boyer-Moore majority vote algorithm.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
         /\ cand' = x
         /\ cnt' = 1
       ELSE IF x = cand THEN
         /\ cnt' = cnt + 1
       ELSE
         /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* The candidate after a complete scan must be the true majority, if one exists.
Correct ==
  \A v \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))
                     => (cand = v)

\* The Boyer-Moore invariant: the candidate is backed by at least cnt votes.
Inv ==
  \A v \in Values : (cnt > 0 /\ cand = v) => (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))

Complete == pos = Len(seq) + 1

====