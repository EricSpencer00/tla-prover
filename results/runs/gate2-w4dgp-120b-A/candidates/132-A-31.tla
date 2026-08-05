---- MODULE MCMajority ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

S == {A, B, C}

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

BoundedSeq(n) == UNION { [1 .. k -> S] : k \in 0 .. n }

InitSeq == UNION { [1 .. k -> S] : k \in 0 .. bound }

TypeOK ==
  /\ seq \in InitSeq
  /\ i \in 1 .. (Len(seq) + 1)
  /\ cand \in S
  /\ cnt \in 0 .. Len(seq)

Init ==
  /\ seq \in InitSeq
  /\ i = 1
  /\ cand \in S
  /\ cnt = 0

Adopt(v) ==
  /\ cnt = 0
  /\ cand' = v
  /\ cnt' = 1
  /\ UNCHANGED <<seq, i>>

Inc(v) ==
  /\ cnt > 0
  /\ cand = v
  /\ cnt' = cnt + 1
  /\ UNCHANGED <<seq, i, cand>>

Dec ==
  /\ cnt > 0
  /\ cand # seq[i]
  /\ cnt' = cnt - 1
  /\ UNCHANGED <<seq, i, cand>>

Next ==
  \/ \E v \in S : Adopt(v)
  \/ \E v \in S : Inc(v)
  \/ Dec
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Correct ==
  \A v \in S : (2 * Cardinality({j \in 1 .. Len(seq) : seq[j] = v}) > Len(seq)) => cand = v

Inv ==
  \A k \in 1 .. Len(seq) : (2 * Cardinality({j \in 1 .. k : seq[j] = cand}) > k) => cnt > 0

Prop == <>(i = Len(seq) + 1)

====