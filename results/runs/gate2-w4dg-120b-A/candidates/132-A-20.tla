---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

VARIABLES sequence, pos, cand, cnt

vars == << sequence, pos, cand, cnt >>

SeqSpace == { s \in [1..len -> Values] : len \in 0..bound }

TypeOK ==
  /\ sequence \in SeqSpace
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ sequence \in SeqSpace
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

ScanNext ==
  /\ pos <= Len(sequence)
  /\ LET x == sequence[pos] IN
       \/ /\ cand # x
          /\ cand' = x
          /\ cnt' = 1
       \/ /\ cand = x
          /\ cnt' = cnt + 1
       \/ /\ cand # x
          /\ cnt' = IF cnt > 0 THEN cnt - 1 ELSE 0
  /\ pos' = pos + 1
  /\ UNCHANGED sequence

Spec == Init /\ [][ScanNext]_vars

Correct ==
  \A e \in Values :
    (2 * Cardinality({ i \in 1..Len(sequence) : sequence[i] = e }) > Len(sequence))
      => (pos = Len(sequence) + 1 /\ cand = e)

Inv ==
  /\ cnt = 0 => \A e \in Values : e # cand
  /\ (cnt > 0 \/ pos = Len(sequence) + 1) => Cardinality({ i \in 1..Len(sequence) : sequence[i] = cand }) >= cnt
  /\ cnt <= Len(sequence)

Next ==
  ScanNext

Properties == Correct /\ Inv

====