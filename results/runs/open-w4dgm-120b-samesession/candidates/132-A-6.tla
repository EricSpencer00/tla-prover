---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

SVals == {A, B, C}
Seqs == UNION { [1 .. n -> SVals] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt
vars == << seq, pos, cand, cnt >>

BoundedSeq == Sequences.Seq

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 0 .. bound
  /\ cand \in SVals
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in SVals
  /\ cnt = 0

Step ==
  /\ pos <= Len(seq)
  /\ IF seq[pos] = cand
       THEN cnt' = cnt + 1
       ELSE IF cnt = 0
              THEN /\ cand' = seq[pos]
                   /\ cnt' = 1
              ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ seq' = seq
  /\ UNCHANGED << >>

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

Correct ==
  /\ \A x \in SVals : 2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = x}) > Len(seq) => x = cand
  /\ \A x \in SVals : 2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = x}) > Len(seq) => cnt > 0

Inv ==
  /\ cnt >= 0
  /\ cnt <= Len(seq)

Completion == (pos > Len(seq)) /\ UNCHANGED vars

Next == Step \/ Completion

Properties == Spec /\ Inv /\ Correct
====