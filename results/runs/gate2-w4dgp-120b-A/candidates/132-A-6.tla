---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

V == {A, B, C}
SeqDomain == UNION {Seq(1..n) : n \in 0..bound}

BoundedSeq == SeqDomain

VARIABLES seq, i, candidate, ctr

vars == <<seq, i, candidate, ctr>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ candidate \in V
    /\ ctr \in Nat

Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ candidate \in V
    /\ ctr = 0

Next ==
    \/ /\ i <= Len(seq)
       /\ LET s == seq[i] IN
            \/ /\ ctr = 0
               /\ candidate' = s
               /\ ctr' = 1
            \/ /\ candidate = s
               /\ ctr' = ctr + 1
            \/ /\ candidate # s
               /\ ctr' = ctr - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i > Len(seq) + 1
       /\ UNCHANGED <<seq, i, candidate, ctr>>

Spec == Init /\ [][Next]_vars

Correct ==
    (Len(seq) > 0 /\ \E k \in 1..Len(seq) : seq[k] = candidate)
        => 2 * Cardinality({j \in 1..Len(seq) : seq[j] = candidate})
              > Len(seq)

Inv ==
    (candidate # A /\ candidate # B /\ candidate # C) => ctr = 0

Post == i = Len(seq) + 1

SpecWeakFairF == Spec /\ WF_vars(Post)

====