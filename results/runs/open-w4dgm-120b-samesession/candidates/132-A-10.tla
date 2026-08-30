---- MODULE MCMajority ----
EXTENDS Sequences
CONSTANTS A, B, C, bound
Values == {A, B, C}
SequencesOfUpToBound == UNION { [1 .. n -> Values] : n \in 0 .. bound }
InitSeq == CHOOSE s \in SequencesOfUpToBound :
             \A t \in SequencesOfUpToBound : Len(t) <= Len(s)
             /\ \A i \in DOMAIN t : t[i] = s[i]

VARIABLES seq, pos, cand, cnt
vars == <<seq, pos, cand, cnt>>

Init ==
  /\ seq \in SequencesOfUpToBound
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next(v) ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                      /\ cnt' = 1
       ELSE IF x = cand THEN cnt' = cnt + 1
       ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][\E v \in Values : Next(v)]_vars
WeakFairness == \A v \in Values : WF_vars(Next(v))

TypeOK ==
  /\ seq \in SequencesOfUpToBound
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. bound

Correct ==
  /\ Len(seq) > 0
  => (pos > Len(seq) => \A i \in 1 .. Len(seq) : seq[i] = cand => (Cnt(seq, cand) * 2 > Len(seq)))

Inv ==
  /\ cnt = 0 \/ cand \in Values
  /\ cnt + (Len(seq) - pos + 1) >= 0

BoundedSeq ==
  seq \in SequencesOfUpToBound
====