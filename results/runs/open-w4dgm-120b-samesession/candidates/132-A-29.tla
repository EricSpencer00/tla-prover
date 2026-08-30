---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
    /\ seq \in [1..bound -> Vals]
    /\ pos \in 1..(bound + 1)
    /\ cand \in Vals
    /\ counter \in 0..bound

Init ==
    /\ seq \in [1..bound -> Vals]
    /\ pos = 1
    /\ cand \in Vals
    /\ counter = 0

ScanStep ==
    /\ pos <= bound
    /\ LET r == seq[pos] IN
         IF counter = 0 THEN
            /\ cand' = r
            /\ counter' = 1
         ELSE IF r = cand THEN
            /\ counter' = counter + 1
            /\ UNCHANGED cand
         ELSE
            /\ counter' = counter - 1
            /\ UNCHANGED cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == ScanStep

Spec == Init /\ [][Next]_vars

CountOccur(v) ==
    Cardinality({i \in 1..bound : seq[i] = v})

Correct ==
    \A v \in Vals : CountOccur(v) > bound / 2 => cand = v

Inv ==
    \A v \in Vals : CountOccur(v) > bound / 2 => cand = v

BoundedSeq == [1..bound -> Vals]

====