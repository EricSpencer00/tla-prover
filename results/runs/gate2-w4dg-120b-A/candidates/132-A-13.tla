---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

Sequences == {s \in [1..n -> Values] : n \in 0..bound}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Sequences
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in Sequences
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

NextRec(a) ==
  /\ pos < Len(seq)
  /\ pos' = pos + 1
  /\ cnt' = IF cnt > 0 /\ seq[pos + 1] = cand THEN cnt + 1
            ELSE IF cnt = 0 THEN 1
            ELSE cnt - 1
  /\ cand' = IF cnt > 0 /\ seq[pos + 1] = cand THEN cand
             ELSE IF cnt = 0 THEN seq[pos + 1]
             ELSE cand
  /\ UNCHANGED seq

Len(f) == Cardinality(Domain(f))

Next ==
  \/ \E a \in Values : NextRec(a)
  \/ \E f \in Sequences : /\ seq' = f
                         /\ pos' = 1
                         /\ UNCHANGED <<cand, cnt>>

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correct ==
  \A e \in Values :
    (cnt > 0 /\ cand = e /\ \A i \in 1..Len(seq) : seq[i] = e)
      => cand = e

Inv ==
  /\ (cnt > 0 => seq[pos] = cand)
  /\ (cnt > 0 => pos <= Len(seq))

====