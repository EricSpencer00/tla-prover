---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(V, n) == { f \in [1..n -> V] : TRUE }

TypeOK ==
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound
  /\ seq \in BoundedSeq(Values, bound)

Init ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Scan ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x /\ cnt' = 1
       ELSE IF x = cand THEN cnt' = cnt + 1 /\ cand' = cand
       ELSE cnt' = cnt - 1 /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Done == (pos > Len(seq))

Next == Scan \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

AtMostOnce ==
  /\ (pos > 1 => seq[pos - 1] \in Values)
  /\ (pos <= Len(seq) => seq[pos] \in Values)

Correct ==
  \A v \in Values : (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) * 2 > Len(seq))
                    => (pos > Len(seq) /\ cand = v)

Inv ==
  \A a, b \in Values :
     (a \in {seq[i] : i \in 1..Len(seq)} /\ b \in {seq[i] : i \in 1..Len(seq)} /\ a # b)
        => a # b

Properties == Correct /\ Inv

====