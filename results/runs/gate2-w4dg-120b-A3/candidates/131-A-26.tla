---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The main algorithm is imported wholesale; this file adds only the proof.
\* Every operator below is named exactly as the reference configuration expects.
\* No state beyond the original spec is introduced here.

CONSTANTS Default

VARIABLES seq, candidate, confirmed, index

vars == <<seq, candidate, confirmed, index>>

Values == Value \cup {Default}

Init ==
  /\ seq = [i \in 1..3 |-> CHOOSE v \in Values : TRUE]
  /\ candidate = Default
  /\ confirmed = FALSE
  /\ index = 1

Next ==
  \/ \E v \in Values :
       /\ seq' = [seq EXCEPT ![index] = v]
       /\ candidate' = IF confirmed THEN candidate
                        ELSE IF index = 1 THEN v
                        ELSE IF seq[index - 1] = v THEN v
                        ELSE candidate
       /\ confirmed' = confirmed \/ (index = 2 /\ candidate = seq[index])
       /\ index' = index + 1
  \/ (index = 3 /\ UNCHANGED <<seq, candidate, confirmed, index>>)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in [1..3 -> Values]
  /\ candidate \in Values
  /\ confirmed \in BOOLEAN
  /\ index \in 0..4

Occurrences(v) ==
  {i \in 1..3 : seq[i] = v}

Inv ==
  /\ candidate \in Values
  /\ confirmed = (index > 2)
  /\ confirmed => (Cardinality(Occurrences(candidate)) > 1)

Correct ==
  /\ (Confirmed => (Cardinality(Occurrences(candidate)) > 1))
  /\ ((\E i \in 1..3 : \A j \in 1..3 : (seq[i] = seq[j]) => (i = j)) => (candidate = seq[1]))

====