---- MODULE MajorityProof ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Value

VARIABLES seq, candidate, pos, seen, exhausted

vars == <<seq, candidate, pos, seen, exhausted>>

Pos == 1..Len(seq)

TypeOK ==
    /\ seq \in Seq(Value)
    /\ candidate \in Value \cup {"none"}
    /\ pos \in Pos
    /\ seen \in [Value -> Pos]
    /\ exhausted \in BOOLEAN

Occur(v, k) == Cardinality({i \in Pos : i <= k /\ seq[i] = v})

Inv ==
    /\ candidate \in Value
    /\ pos \in Pos
    /\ seen[v] = 0
    /\ \A w \in Value: w # v => seen[w] = 0

Init ==
    /\ seq \in Seq(Value)
    /\ Len(seq) >= 1
    /\ candidate = "none"
    /\ pos = 1
    /\ seen = [v \in Value |-> 0]
    /\ exhausted = FALSE

Admit(v) ==
    /\ candidate = "none"
    /\ candidate' = v
    /\ UNCHANGED <<seq, pos, seen, exhausted>>

Match(v) ==
    /\ candidate # "none"
    /\ seq[pos] = v
    /\ seen' = [seen EXCEPT ![v] = pos]
    /\ pos' = IF pos < Len(seq) THEN pos + 1 ELSE pos
    /\ exhausted' = IF pos = Len(seq) THEN TRUE ELSE exhausted
    /\ UNCHANGED <<seq, candidate>>

Mismatch(v) ==
    /\ candidate # "none"
    /\ seq[pos] # v
    /\ candidate' = "none"
    /\ seen' = [w \in Value |-> 0]
    /\ UNCHANGED <<seq, pos, exhausted>>

Next ==
    \/ \E v \in Value: Admit(v)
    \/ \E v \in Value: Match(v)
    \/ \E v \in Value: Mismatch(v)

Spec == Init /\ [][Next]_vars

Majority(v) ==
    /\ Len(seq) % 2 = 1
    /\ 2 * Occur(v, Len(seq)) > Len(seq)
    /\ candidate = v

Correct == \A v \in Value: Majority(v) => (candidate = v /\ pos = Len(seq))

====