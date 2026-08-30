---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajoritySpec

CONSTANTS Value

VARIABLES scanned, candidate, steps, ballot

vars == <<scanned, candidate, steps, ballot>>

TypeOK ==
  /\ scanned \in 0..len
  /\ candidate \in ({}) \cup Value
  /\ steps \in {"idle", "tallying", "finished"}
  /\ ballot \subseteq (0..(len - 1))

Init ==
  /\ scanned = 0
  /\ candidate = {}
  /\ steps = "idle"
  /\ ballot = {}

Start ==
  /\ steps = "idle"
  /\ candidate' = CHOOSE e \in seq : TRUE
  /\ ballot' = {}
  /\ steps' = "tallying"
  /\ UNCHANGED scanned

Tally ==
  /\ steps = "tallying"
  /\ scanned < len
  /\ ballot' = ballot \cup {scanned}
  /\ scanned' = scanned + 1
  /\ UNCHANGED <<candidate, steps>>

Finish ==
  /\ steps = "tallying"
  /\ scanned = len
  /\ steps' = "finished"
  /\ UNCHANGED <<scanned, candidate, ballot>>

Next == Start \/ Tally \/ Finish

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ steps # "finished" => scanned < len
  /\ steps = "tallying" => candidate \in Value

Correct ==
  /\ steps = "finished"
  /\ scanned = len
  /\ \A e \in Value : (2 * Cardinality({i \in 0..(len - 1) : seq[i] = e}) > len) => e = candidate

====