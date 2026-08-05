---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* BoundedSeq replaces Sequences!Seq with a version that only builds
\* sequences up to a given maximum length, so the state space stays finite.
BoundedSeq == UNION { [1..n -> {A, B, C}] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in Nat
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

\* The Boyer-Moore scan: move the candidate/adopt/retire logic as the scan
\* head advances, one step per action.
Step ==
  /\ i <= Len(seq)
  /\ \/ /\ cnt = 0
        /\ cand' = seq[i]
        /\ cnt' = 1
     \/ /\ seq[i] = cand
        /\ cnt' = cnt + 1
        /\ cand' = cand
     \/ /\ seq[i] # cand
        /\ cnt > 0
        /\ cnt' = cnt - 1
        /\ cand' = cand
  /\ i' = i + 1

Next == Step

Spec == Init /\ [][Next]_vars

\* Any element that truly is a majority of the whole sequence must be
\* exactly the candidate left after the scan completes.
Correct == \A x \in {A, B, C}: (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => (cand = x)

\* The Boyer-Moore state invariant: the counter never exceeds the number
\* of positions scanned so far, so it can never drop below zero.
Inv == cnt <= i

Complete == <>(i > Len(seq))

ASSUME /\ bound \in Nat

====