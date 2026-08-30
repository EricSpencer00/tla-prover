---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
Seqs == {f \in [1 .. bound -> Values] : \E n \in 0 .. bound : f \in [1 .. n -> Values]}
BoundedSeq == Sequences.Seq

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET e == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = e
                     /\ cnt' = 1
       ELSE IF e = cand THEN /\ cand' = cand
                           /\ cnt' = cnt + 1
       ELSE /\ cand' = cand
            /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Done == pos = Len(seq) + 1

Next == Scan \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Correct ==
  \A e \in Values : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = e}) > Len(seq)) => e = cand

Inv == \A e \in Values : (2 * Cardinality({i \in 1 .. Len(seq) : seq[i] = e}) > Len(seq)) => e = cand

====