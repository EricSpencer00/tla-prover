---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Value

VARIABLES seq, candidate, count, visited, seen

vars == <<seq, candidate, count, visited, seen>>

Majority == Cardinality(seq) \div 2 + 1

IsMajority(v) == Cardinality({i \in 1 .. Cardinality(seq) : seq[i] = v}) >= Majority

TypeOK ==
    /\ seq \in Seq(Value)
    /\ candidate \in Value
    /\ count \in Nat
    /\ visited \in 0 .. Cardinality(seq)
    /\ seen \subseteq Value

Init ==
    /\ seq = << >>
    /\ candidate = CHOOSE v \in Value : TRUE
    /\ count = 0
    /\ visited = 0
    /\ seen = {}

Append(v) ==
    /\ seq' = Append(seq, v)
    /\ UNCHANGED <<candidate, count, visited, seen>>

Vote ==
    /\ visited < Cardinality(seq)
    /\ LET p == seq[visited + 1] IN
        IF count = 0 THEN
            /\ candidate' = p
            /\ count' = 1
            /\ seen' = seen \cup {p}
        ELSE
            /\ IF p = candidate THEN count' = count + 1
               ELSE count' = count - 1
            /\ seen' = seen \cup {p}
    /\ visited' = visited + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Vote]_vars

Inv ==
    /\ visited <= Cardinality(seq)
    /\ visited > 0 => candidate \in seen
    /\ visited > 0 /\ visited <= Cardinality(seq) => seq[visited] \in seen
    /\ \/ \A v \in seen : Cardinality({i \in 1 .. visited : seq[i] = v}) >= count
          \/ count = 0

TypeOKProp == TypeOK

Correct == Inv

====