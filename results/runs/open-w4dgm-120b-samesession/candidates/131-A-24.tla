---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

StateSpace == {"idle", "scanning", "done"}

VARIABLES seq, candidate, count, scanned, phase

vars == <<seq, candidate, count, scanned, phase>>

RECURSIVE CountOccurrences(_)
CountOccurrences(n) ==
  IF n < 1 THEN 0
  ELSE (IF seq[n] = candidate THEN 1 ELSE 0) + CountOccurrences(n - 1)

Tally == CountOccurrences(Len(seq))

TypeOK ==
  /\ seq \in [1..Len(seq) -> Value]
  /\ candidate \in Value
  /\ count \in 0..Len(seq)
  /\ scanned \in 0..Len(seq)
  /\ phase \in StateSpace

Inv ==
  /\ ((phase = "idle") =>
        /\ scanned = 0
        /\ count = 0
        /\ candidate \in Value)
  /\ ((phase = "scanning") => scanned < Len(seq))

Init ==
  /\ \E s \in [1..Len(seq) -> Value] :
        seq = s
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ scanned = 0
  /\ phase = "idle"

Start ==
  /\ phase = "idle"
  /\ phase' = "scanning"
  /\ UNCHANGED <<seq, candidate, count, scanned>>

TallyStep ==
  /\ phase = "scanning"
  /\ scanned < Len(seq)
  /\ scanned' = scanned + 1
  /\ count' = IF seq[scanned + 1] = candidate THEN count + 1 ELSE count
  /\ UNCHANGED <<seq, candidate, phase>>

Finish ==
  /\ phase = "scanning"
  /\ scanned = Len(seq)
  /\ phase' = "done"
  /\ UNCHANGED <<seq, candidate, count, scanned>>

Restart ==
  /\ phase = "done"
  /\ phase' = "idle"
  /\ count' = 0
  /\ scanned' = 0
  /\ UNCHANGED <<seq, candidate>>

Next ==
  \/ Start
  \/ TallyStep
  \/ Finish
  \/ Restart

Spec == Init /\ [][Next]_vars

Correct ==
  /\ (scanned = Len(seq) => phase = "done")
  /\ (phase = "done" => count = Tally)

====