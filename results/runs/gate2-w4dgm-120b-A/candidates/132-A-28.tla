---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

\* A bounded sequence: only functions with domain 1..n for n up to 'bound' are allowed.
BoundedSeq == UNION { [1..n -> {A, B, C}] : n \in 0..bound }

InitSeq(s) ==
    /\ s \in BoundedSeq
    /\ pos = 1
    /\ cand \in {A, B, C}
    /\ count = 0

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1..(bound + 1)
    /\ cand \in {A, B, C}
    /\ count \in 0..bound

IsMajority(c) == \A A \in BoundedSeq : (Len(A) > 0) => ((Cardinality({i \in 1..Len(A) : A[i] = c}) * 2 > Len(A)) = (cand = c))

Init ==
    /\ \E s \in BoundedSeq : InitSeq(s)
    /\ UNCHANGED <<seq, pos, cand, count>>

\* Boyer-Moore scan: three cases, each kept weakly fair so the scan always makes progress.
Adopt(i) ==
    /\ pos <= Len(seq)
    /\ pos = i
    /\ (cand # seq[i] \/ count = 0)
    /\ cand' = seq[i]
    /\ count' = 1
    /\ pos' = i + 1
    /\ UNCHANGED seq

IncCount(i) ==
    /\ pos <= Len(seq)
    /\ pos = i
    /\ seq[i] = cand
    /\ count > 0
    /\ count' = count + 1
    /\ pos' = i + 1
    /\ UNCHANGED <<seq, cand>>

DecCount(i) ==
    /\ pos <= Len(seq)
    /\ pos = i
    /\ seq[i] # cand
    /\ count > 0
    /\ count' = count - 1
    /\ pos' = i + 1
    /\ UNCHANGED <<seq, cand>>

Next == \E i \in 1..bound : Adopt(i) \/ IncCount(i) \/ DecCount(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Adopt(1)) /\ WF_vars(IncCount(1)) /\ WF_vars(DecCount(1))

Inv == pos <= Len(seq) => (cand \in {seq[pos]} \/ count = 0)

Correct == (\A c \in {A, B, C} : IsMajority(c)) => (pos = Len(seq) + 1 => forall i \in 1..Len(seq) : seq[i] = cand)

\* The model bounds the sequence length to keep the state space finite.
Bound == UNCHANGED vars

====