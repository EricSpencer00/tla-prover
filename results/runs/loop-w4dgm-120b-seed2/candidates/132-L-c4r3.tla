---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
SeqSpace == UNION {[1 .. n -> Values] : n \in 0 .. bound}

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

BoundedSeq == SeqSpace

Init ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ cnt = 0

Match(v) == IF seq[pos] = v THEN cnt + 1 ELSE cnt - 1

ScanStep ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       /\ cand' = IF cnt = 0 THEN v ELSE cand
       /\ cnt' = Match(v)
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Done == pos > Len(seq)

Next == ScanStep \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(ScanStep)

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Correct ==
  \A v \in Values : (Cardinality({i \in 1 .. Len(seq) : seq[i] = v}) > Len(seq) \div 2) => (v = cand)

Inv ==
  /\ cnt = 0 => cand \in Values
  /\ cnt >= 1 => (pos > 1 /\ seq[pos - 1] = cand)

FullScan == (pos > Len(seq)) ~> (pos = 1)
====