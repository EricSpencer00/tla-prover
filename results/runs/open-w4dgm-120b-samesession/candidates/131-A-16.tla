---- MODULE MajorityProof ----
EXTENDS MajoritySpec, FiniteSets

CONSTANTS Value

Bump == 1

VARIABLES seq, pos, candidate, majorityValue, voted, checked

vars == <<seq, pos, candidate, majorityValue, voted, checked>>

TypeOK ==
    /\ seq \in [1..3 -> {Value, "none"}]
    /\ pos \in 0..3
    /\ candidate \in {Value, "none"}
    /\ majorityValue \in {Value, "none"}
    /\ voted \subseteq 1..3
    /\ checked \subseteq 1..3

Occurrences(v, S) == Cardinality({i \in S : seq[i] = v})

Inv ==
    /\ pos \in 0..3
    /\ candidate \in {Value, "none"}
    /\ majorityValue \in {Value, "none"}
    /\ voted \subseteq 1..3
    /\ checked \subseteq 1..3
    /\ (candidate # "none" => majorityValue = "none")
    /\ pos = 3 => checked = 1..3

Init ==
    /\ seq = [i \in 1..3 |-> IF i = 2 THEN Value ELSE "none"]
    /\ pos = 0
    /\ candidate = "none"
    /\ majorityValue = "none"
    /\ voted = {}
    /\ checked = {}

Vote(i) ==
    /\ i \in 1..3
    /\ i \notin voted
    /\ voted' = voted \union {i}
    /\ UNCHANGED <<seq, pos, candidate, majorityValue, checked>>

BeginNewRound ==
    /\ pos = 3
    /\ pos' = 0
    /\ candidate' = "none"
    /\ majorityValue' = "none"
    /\ voted' = {}
    /\ checked' = {}
    /\ UNCHANGED seq

Check(i) ==
    /\ candidate = "none"
    /\ i \in 1..3
    /\ i \notin checked
    /\ checked' = checked \union {i}
    /\ candidate' = IF i \in voted THEN seq[i] ELSE "none"
    /\ UNCHANGED <<seq, pos, majorityValue, voted>>

Advance ==
    /\ pos < 3
    /\ pos' = pos + 1
    /\ majorityValue' = IF candidate # "none" /\ 2 * Occurrences(candidate, 1..(pos + 1)) > (pos + 1)
                        THEN candidate ELSE "none"
    /\ UNCHANGED <<seq, candidate, voted, checked>>

Next ==
    \/ \E i \in 1..3 : Vote(i)
    \/ BeginNewRound
    \/ \E i \in 1..3 : Check(i)
    \/ Advance

Spec == Init /\ [][Next]_vars

====