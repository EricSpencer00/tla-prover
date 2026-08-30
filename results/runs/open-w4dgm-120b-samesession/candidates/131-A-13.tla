---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajoritySpec

CONSTANTS Value

VARIABLES seq, scanned, candidate, count, totalScanned

vars == <<seq, scanned, candidate, count, totalScanned>>

TypeOK ==
    /\ seq \in [1..3 -> Value \cup {"none"}]
    /\ scanned \subseteq 1..3
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..3
    /\ totalScanned \in 0..3

Init ==
    /\ seq = [i \in 1..3 |-> "none"]
    /\ scanned = {}
    /\ candidate = "none"
    /\ count = 0
    /\ totalScanned = 0

Write(i, v) ==
    /\ i \notin scanned
    /\ seq' = [seq EXCEPT ![i] = v]
    /\ scanned' = scanned \cup {i}
    /\ totalScanned' = totalScanned + 1
    /\ candidate' = IF candidate = "none" THEN v
                    ELSE IF v = candidate THEN candidate
                    ELSE "none"
    /\ count' = IF candidate = "none" THEN IF v # "none" THEN 1 ELSE count
               ELSE IF v = candidate THEN count + 1 ELSE count - 1

Skip(i) ==
    /\ i \notin scanned
    /\ seq' = [seq EXCEPT ![i] = "none"]
    /\ scanned' = scanned \cup {i}
    /\ totalScanned' = totalScanned + 1
    /\ UNCHANGED <<candidate, count>>

Spec == Init /\ [][Write]_vars /\ [][Skip]_vars

Corrections(z) == IF seq[z] = "none" THEN 0 ELSE 1

Occurrences(n) == Cardinality({i \in 1..3 : seq[i] = n})

Inv ==
    /\ count = IF candidate = "none" THEN 0 ELSE Occurrences(candidate)
    /\ totalScanned = Cardinality(scanned)

Correct == candidate # "none" => 2 * Occurrences(candidate) > totalScanned

====