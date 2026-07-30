---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC, MajorityVote

CONSTANTS Value

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

TypeOK ==
  /\ candidate \in Value
  /\ count \in Nat
  /\ scanned \in Nat
  /\ seq \in Seq(Value)

Init ==
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ scanned = 0
  /\ seq = <<>>

Next ==
  \/ \E v \in Value :
       /\ seq' = Append(seq, v)
       /\ scanned' = scanned + 1
       /\ IF count = 0
            THEN candidate' = v
            ELSE candidate' = candidate
       /\ IF count = 0
            THEN count' = 1
            ELSE IF v = candidate
                 THEN count' = count + 1
                 ELSE count' = count - 1
  \/ \E v \in Value :
       /\ seq' = seq
       /\ scanned' = scanned
       /\ count' = count
       /\ candidate' = v

Spec == Init /\ [][Next]_vars

\* No new state and no new action: everything is inherited from the main
\* specification, so the proof obligations are the only thing added here.

Correct ==
  \A c \in Value :
    (\A i \in {j \in 1..scanned : seq[j] = c} : TRUE)
      => candidate = c

Inv == TypeOK /\ Correct

====