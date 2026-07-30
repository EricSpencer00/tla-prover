---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}
Seqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Step ==
  /\ pos <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[pos]
            /\ cnt' = 1
       ELSE IF seq[pos] = cand
            THEN cnt' = cnt + 1
            ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, cand>>

Next == Step

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

Count(x) == Cardinality({ i \in 1 .. Len(seq) : seq[i] = x })

Correct ==
  /\ pos = Len(seq) + 1
  /\ \E x \in Values : Count(x) > Len(seq) / 2 => x = cand

Inv ==
  /\ cnt >= 0
  /\ \A x \in Values : cnt > 0 => cand = x => Count(x) > 0
  /\ \A x \in Values : cnt >= 0 => Count(x) >= cnt

Complete == pos = Len(seq) + 1

====