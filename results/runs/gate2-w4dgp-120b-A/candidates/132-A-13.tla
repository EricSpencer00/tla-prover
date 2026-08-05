---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

BoundedSeq == { f \in [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ \E s \in BoundedSeq : seq = s
  /\ pos = 1
  /\ \E c \in Values : cand = c
  /\ cnt = 0

Next ==
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ cand = v
       /\ cnt > 0
       /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq, cand>>
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ cand # v
       /\ cnt = 0
       /\ cand' = v
       /\ cnt' = 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq>>
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ cand # v
       /\ cnt > 0
       /\ cand' = cand
       /\ cnt' = cnt + 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Correct ==
  \A v \in Values :
    ( Cardinality({ i \in 1..Len(seq) : seq[i] = v }) * 2 > Len(seq) )
      => cand = v

Inv ==
  cnt <= Len(seq) /\ pos <= Len(seq) + 1

Progress == (pos = 1) ~> (pos > Len(seq))

====