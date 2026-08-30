---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A bounded sequence: the usual Seq constructor, but only over the finite
\* domain [1..bound], so the model stays finite for checking.
BoundedSeq(S) == { f \in [1..bound -> Values] : \A i \in 1..bound : f[i] \in S }

VARIABLES seq, pos, cand, count

vars == << seq, pos, cand, count >>

Seqlen == Len(seq)
Rest == SubSeq(seq, pos + 1, Seqlen)

TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in 0..bound
    /\ cand \in Values
    /\ count \in 0..bound

\* A true majority must be the final candidate after a completed scan.
Correct ==
    /\ ((2 * count > Seqlen) <=> (cand = Rest[1]))
    /\ (Seqlen > 0 => cand \in Values)

Init ==
    \E s \in BoundedSeq(Values) :
        /\ seq = s
        /\ pos = 1
        /\ cand \in Values
        /\ count = 0

Scan ==
    /\ pos <= Seqlen
    /\ IF pos > Seqlen
       THEN UNCHANGED vars
       ELSE IF count = 0 \/ seq[pos] # cand
             THEN cand' = seq[pos] /\ count' = 1
             ELSE count' = count + 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Scan

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Scan)

Inv == TypeOK /\ Correct

Completion == pos > Seqlen

====