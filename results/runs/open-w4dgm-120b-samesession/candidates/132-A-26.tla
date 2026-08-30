---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

BoundedSeq(E, n) == { f \in [1..n -> E] }

TypeOK ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in Nat

Init ==
    /\ seq \in BoundedSeq(Values, bound)
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

ScanNext ==
    /\ pos <= Len(seq)
    /\ LET v == seq[pos] IN
        /\ IF count = 0 THEN cand' = v ELSE cand' = cand
        /\ count' = IF count = 0 \/ v = cand THEN count + 1 ELSE count - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == ScanNext

Spec == Init /\ [][Next]_vars
    /\ WF_vars(ScanNext)

Correct ==
    /\ (pos > Len(seq)) => (If 2 * count > Len(seq) then cand = seq[1 else TRUE)

Inv ==
    /\ (pos > Len(seq)) => (2 * count <= Len(seq) \/ cand = seq[1])

====