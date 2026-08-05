---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

BoundedSeq(n) == UNION { { f \in [1..k -> Values] } : k \in 0..n }

TypeOK ==
  /\ seq \in BoundedSeq(bound)
  /\ pos \in Nat
  /\ cand \in Values
  /\ counter \in Nat

Init ==
  /\ seq \in BoundedSeq(bound)
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

Process ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       IF counter = 0
       THEN /\ cand' = v
            /\ counter' = 1
       ELSE IF cand = v
            THEN counter' = counter + 1
                 cand' = cand
            ELSE counter' = counter - 1
                 cand' = cand
  /\ pos' = pos + 1

Done ==
  /\ pos > Len(seq)
  /\ UNCHANGED <<seq, pos, cand, counter>>

Next == Process \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Process)

Correct ==
  ( \E i \in 1..Len(seq) : (\A j \in 1..Len(seq) : seq[i] = seq[j]) )
    => cand = seq[1]

Inv ==
  (counter > 0) => (cand = seq[pos - 1])

StateBound == Len(seq) <= bound

====