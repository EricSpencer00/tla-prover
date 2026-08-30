---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSets, Naturals, Integers

CONSTANTS Value

VARIABLES seq, scanned, candidate, scanPos

vars == <<seq, scanned, candidate, scanPos>>

\* A value occurs more than half the time strictly before scanPos.
Majority(v) == 2 * Cardinality(positions(seq, scanned, v) \cap (1 .. (scanPos - 1))) > scanPos - 1

TypeOK ==
    /\ seq \in UNION [p \in 1 .. Len(seq) |-> [1 .. p -> Value]]
    /\ scanned \subseteq 1 .. Len(seq)
    /\ candidate \in Value
    /\ scanPos \in 1 .. (Len(seq) + 1)

\* After a full scan, any strict-majority value must be the candidate.
Correct == (scanPos = Len(seq) + 1) => (\A v \in Value : Majority(v) => v = candidate)

Init ==
    /\ \E v \in Value : seq = <<v>>
    /\ scanned = {}
    /\ candidate = CHOOSE v \in Value : TRUE
    /\ scanPos = 1

Scope(k) ==
    /\ k >= 1
    /\ Len(seq < k
    /\ scanPos = Len(seq) + 1
    /\ \E v \in Value : seq' = Append(seq, v)
    /\ UNCHANGED <<scanned, candidate, scanPos>>

Next == Scope(3)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ Correct

====