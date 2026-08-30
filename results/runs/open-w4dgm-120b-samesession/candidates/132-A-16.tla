---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

BoundedSeq(f) == { k \in 1..Len(f) : f[k] \in Values }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

Init ==
    /\ \E s \in { f \in [1..n -> Values] : n \in 0..bound } : seq = s
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

ScanNext ==
    /\ pos <= Len(seq) + 1
    /\ pos' = pos + 1
    /\ count' = IF pos <= Len(seq) THEN
                    IF seq[pos] = cand THEN count + 1
                    ELSE IF count = 0 THEN count + 1 /\ cand' = seq[pos]
                    ELSE count - 1
                ELSE count
    /\ UNCHANGED seq
    /\ UNCHANGED cand

Spec == Init /\ [][ScanNext]_vars
    /\ WF_vars(ScanNext)

TypeOK ==
    /\ seq \in { f \in [1..n -> Values] : n \in 0..bound }
    /\ pos \in 1..(bound + 2)
    /\ cand \in Values
    /\ count \in 0..bound

Correct ==
    /\ \A x \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq))
        => (pos = Len(seq) + 1 /\ cand = x)

Inv ==
    /\ pos \in 1..(Len(seq) + 1)
    /\ count \in 0..Len(seq)

Completion == pos = Len(seq) + 1

====