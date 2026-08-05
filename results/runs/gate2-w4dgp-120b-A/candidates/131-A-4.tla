---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

DOMAIN == (Int \ {0}) \X Value

VARIABLES seq, cand, yes, no, i

vars == <<seq, cand, yes, no, i>>

Before(i) == {k \in 1..(i - 1) : seq[k] = cand}
After(i) == {k \in (i + 1)..Len(seq) : seq[k] = cand}

TypeOK ==
  /\ seq \in DOMAIN
  /\ cand \in Value
  /\ yes \in 0..Len(seq)
  /\ no \in 0..Len(seq)
  /\ i \in 1..(Len(seq) + 1)

Init ==
  /\ seq \in DOMAIN
  /\ cand = seq[1]
  /\ yes = 1
  /\ no = 0
  /\ i = 2

Accept ==
  /\ i <= Len(seq)
  /\ seq[i] = cand
  /\ yes < Len(seq)
  /\ yes' = yes + 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, cand, no>>

Reject ==
  /\ i <= Len(seq)
  /\ seq[i] # cand
  /\ no < yes
  /\ no' = no + 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, cand, yes>>

Replace ==
  /\ i <= Len(seq)
  /\ seq[i] # cand
  /\ yes = no
  /\ cand' = seq[i]
  /\ yes' = 1
  /\ no' = 0
  /\ i' = i + 1
  /\ UNCHANGED <<seq>>

Advance ==
  /\ i <= Len(seq)
  /\ yes < no
  /\ no' = 0
  /\ i' = i + 1
  /\ UNCHANGED <<seq, cand, yes>>

End == /\ i = Len(seq) + 1 /\ UNCHANGED vars

Next == Accept \/ Reject \/ Replace \/ Advance \/ End

Spec == Init /\ [][Next]_vars

Inv ==
  /\ yes = Cardinality(Before(i + 1))
  /\ no = Cardinality(After(i))

Correct ==
  /\ i = Len(seq) + 1
  /\ (yes > Len(seq) / 2 => cand = seq[1])

====