---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

SeqSpace == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, ctr
vars == << seq, pos, cand, ctr >>

TypeOK ==
    /\ seq \in SeqSpace
    /\ pos \in 1 .. (Len(seq) + 1)
    /\ cand \in Values
    /\ ctr \in Nat

Init ==
    /\ seq \in SeqSpace
    /\ pos = 1
    /\ cand \in Values
    /\ ctr = 0

Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        IF ctr = 0 THEN
            /\ cand' = x
            /\ ctr' = 1
        ELSE IF cand = x THEN
            /\ ctr' = ctr + 1
        ELSE
            /\ ctr' = ctr - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec == Init /\ [][Next]_vars

Correct ==
    (pos = Len(seq) + 1 /\ ctr > 0) => (cand = Cardinality({i \in 1 .. Len(seq) : seq[i] = cand}) * 2 > Len(seq))

Inv ==
    /\ cand \in Values
    /\ ctr <= Len(seq)
    /\ (pos = 1) => (ctr = 0)

====