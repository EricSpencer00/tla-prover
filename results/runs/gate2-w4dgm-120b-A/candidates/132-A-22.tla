---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

M == {A, B, C}
Seqs == UNION { [1 .. n -> M] : n \in 0 .. bound }

VARIABLES seq, pos, cand, ctr

vars == << seq, pos, cand, ctr >>

BoundedSeq(S, n) == { f \in S : Len(f) = n }

TypeOK ==
    /\ seq \in SeqS
    /\ pos \in 1 .. bound + 1
    /\ cand \in M
    /\ ctr \in 0 .. bound

Init ==
    /\ seq \in SeqS
    /\ pos = 1
    /\ cand \in M
    /\ ctr = 0

Next ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         \/ /\ x = cand
            /\ ctr < bound
            /\ ctr' = ctr + 1
            /\ cand' = cand
         \/ /\ x # cand
            /\ ctr' = 0
            /\ cand' = x
         \/ /\ cand' = cand
            /\ ctr' = ctr
    /\ pos' = pos + 1
    /\ seq' = seq

Spec == Init /\ [][Next]_vars

Correct ==
    \A e \in M : (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = e }) > Len(seq))
                     => (cand = e /\ pos = Len(seq) + 1)

Inv ==
    /\ (pos > Len(seq) => ctr = 0)
    /\ (~(pos > Len(seq) /\ cand # seq[1]) => cand # seq[1])

SeqS == SeqBounded(bound)
SeqBounded(n) == UNION { BoundedSeq([1 .. k -> M], k) : k \in 0 .. n }

ScanComplete == pos > Len(seq)
WeakFairness == SF_vars(ScanComplete)

====