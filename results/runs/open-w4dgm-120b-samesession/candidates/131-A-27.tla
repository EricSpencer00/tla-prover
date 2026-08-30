---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

ASSUME Value \in NONEMPTY

VARIABLES seq, pos, cand, phase, decisions

vars == <<seq, pos, cand, phase, decisions>>

TypeOK ==
    /\ seq \in Seq(Value)
    /\ pos \in 0..Len(seq)
    /\ cand \in Value
    /\ phase \in {"counting", "decided"}
    /\ decisions \subseteq [value: Value, count: 0..Len(seq)]

Init ==
    /\ seq = <<>>
    /\ pos = 0
    /\ cand = CHOOSE v \in Value : TRUE
    /\ phase = "counting"
    /\ decisions = {}

Append(v) ==
    /\ SeqLen(seq) < 3
    /\ seq' = AppendSeq(seq, v)
    /\ UNCHANGED <<pos, cand, phase, decisions>>

Elect(v) ==
    /\ phase = "counting"
    /\ cand' = v
    /\ UNCHANGED <<seq, pos, phase, decisions>>

Count(v) ==
    /\ phase = "counting"
    /\ pos < Len(seq)
    /\ seq[pos] = v
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, cand, phase, decisions>>

SkipMove ==
    /\ phase = "counting"
    /\ pos < Len(seq)
    /\ seq[pos] # cand
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, cand, phase, decisions>>

Decide ==
    /\ phase = "counting"
    /\ pos = Len(seq)
    /\ phase' = "decided"
    /\ decisions' = decisions \cup {[value |-> cand, count |-> Cardinality({i \in 0..(pos - 1) : seq[i] = cand}])}
    /\ UNCHANGED <<seq, pos, cand>>

Restart ==
    /\ phase = "decided"
    /\ phase' = "counting"
    /\ decisions' = {}
    /\ pos' = 0
    /\ UNCHANGED <<seq, cand>>

Next ==
    \/ \E v \in Value : Append(v)
    \/ \E v \in Value : Elect(v)
    \/ \E v \in Value : Count(v)
    \/ SkipMove
    \/ Decide
    \/ Restart

Spec == Init /\ [][Next]_vars

Correct ==
    /\ (\A d \in decisions : d.value = cand)
    /\ \A v \in Value : (Cardinality({i \in 0..(Len(seq) - 1) : seq[i] = v}) * 2 > Len(seq)) => v = cand

Inv == TypeOK /\ Correct

====