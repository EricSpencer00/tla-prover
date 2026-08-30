---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

SequencesOf(B) == UNION { [1..n -> Values] : n \in 0..B }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

Init ==
    /\ seq \in SequencesOf(bound)
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Adopt ==
    /\ pos <= Len(seq)
    /\ seq[pos] # cand
    /\ count = 0
    /\ cand' = seq[pos]
    /\ count' = 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Match ==
    /\ pos <= Len(seq)
    /\ seq[pos] = cand
    /\ count < bound
    /\ count' = count + 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, cand>>

Reduce ==
    /\ pos <= Len(seq)
    /\ seq[pos] # cand
    /\ count > 0
    /\ count' = count - 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, cand>>

Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED vars

Next == Adopt \/ Match \/ Reduce \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Adopt) /\ WF_vars(Match) /\ WF_vars(Reduce)

TypeOK ==
    /\ seq \in SequencesOf(bound)
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Correct ==
    (Len(seq) > 0 /\ \E m \in 1..Len(seq) : (\A j \in 1..Len(seq) : seq[j] = seq[m]) => seq[m] = cand)

Inv ==
    /\ (pos > Len(seq) => count = 0)
    /\ (pos > 1 => \A j \in 1..(pos - 1) : (seq[j] = cand) <=> (j <= count + 1))

Complete == (\E v \in Values : CandAt(v) = Len(seq))

CandAt(v) == Cardinality({ i \in 1..(Len(seq) + 1) : seq[i] = v })

====