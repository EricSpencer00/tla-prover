---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

BoundedSeq(S) == \E n \in 0..bound : S = [1..n -> Values]

Init ==
  /\ BoundedSeq(seq)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

ScanStep ==
  /\ pos <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[pos]
            /\ cnt' = 1
       ELSE IF seq[pos] = cand
            THEN cnt' = cnt + 1
            ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq>>

Spec == Init /\ [][ScanStep]_vars
  /\ WF_vars(ScanStep)
  /\ WF_vars(ScanStep)

TypeOK ==
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat
  /\ BoundedSeq(seq)

Correct ==
  /\ pos = Len(seq) + 1
  /\ (\A v \in Values : 2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => (cand = seq[1])

Inv ==
  /\ (\A v \in Values : 2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => (cand = seq[1])
  /\ cnt <= Len(seq)
  /\ pos \in 1..(Len(seq) + 1)

====