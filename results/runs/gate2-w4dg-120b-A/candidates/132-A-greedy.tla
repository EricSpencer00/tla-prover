---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Seqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

TypeOK ==
  /\ seq \in Seq
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ seq[pos] = v
       /\ IF cnt = 0 THEN cand' = v /\ cnt' = 1
          ELSE IF v = cand THEN cnt' = cnt + 1 /\ cand' = cand
          ELSE cnt' = cnt - 1 /\ cand' = cand
       /\ pos' = pos + 1
       /\ UNCHANGED seq
  \/ \E v \in Values :
       /\ pos > Len(seq)
       /\ seq' = [1 .. Len(seq) + 1 |-> v]
       /\ pos' = 1
       /\ cand' = v
       /\ cnt' = 0

Spec == Init /\ [][Next]_vars

Correct ==
  (cnt > 0 /\ pos = Len(seq) + 1) => \A i \in 1 .. Len(seq) : seq[i] = cand

Inv ==
  /\ cnt >= 0
  /\ cnt <= Len(seq)
  /\ (cnt = 0 => cand \in Values)

SpecOK == Spec

====