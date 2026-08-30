---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

Seqs == Union({[1 .. n -> Values] : n \in 0 .. bound})

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Init ==
  /\ \E s \in Seqs : seq = s
  /\ pos = 1
  /\ \E v \in Values : cand = v
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       cand' = IF cnt = 0 THEN x ELSE IF x = cand THEN cand ELSE cand
       \/ cnt' = IF cnt = 0 THEN 1
                  ELSE IF x = cand THEN cnt + 1
                  ELSE cnt - 1
  /\ pos' = pos + 1

Reset ==
  /\ pos > Len(seq)
  /\ pos' = 1
  /\ cand' = cand
  /\ cnt' = 0
  /\ \E v \in Values : cand' = v
  /\ seq' = seq

Next == Scan \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

Correct ==
  /\ pos > 1 => (cnt = 0 \/ cand = seq[pos - 1])
  /\ pos > Len(seq) => (cnt = 0 \/ cand = seq[Len(seq)])

Inv ==
  /\ cnt <= Len(seq)
  /\ (cnt > 0 => cand \in {seq[i] : i \in 1 .. Len(seq)})

BoundedSeq == Sequences.Seq
====