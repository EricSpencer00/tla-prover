---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The value set of the three distinct elements sequences are drawn from.
Values == {A, B, C}

SequenceOf(n) == [i \in 1..n |-> CHOOSE v \in Values : TRUE]

\* BoundedSeq is a finite, bounded-length version of Seq, used to keep the
\* model state space finite for exhaustive checking (replaces Seq).
BoundedSeq(S) == CHOOSE seq \in [1..bound -> Values] : seq = S

\* ScanE: the element currently being scanned (1 = first element).
\* Candidate: the majority vote candidate; Counter: the Boyer-Moore counter.
VARIABLES S, ScanE, Candidate, Counter

vars == <<S, ScanE, Candidate, Counter>>

TypeOK ==
    /\ ScanE \in 1..bound
    /\ Candidate \in Values
    /\ Counter \in 0..bound

Init ==
    /\ S \in {BoundedSeq(SequenceOf(k)) : k \in 0..bound}
    /\ ScanE = 1
    /\ Candidate \in Values
    /\ Counter = 0

\* The standard Boyer-Moore scan step, with the three cases.
NextEl(c) == IF c # S[ScanE] THEN c ELSE Candidate

ScanStep ==
    /\ ScanE <= Len(S)
    /\ ScanE' = ScanE + 1
    /\ Candidate' = NextEl(Candidate)
    /\ Counter' = IF S[ScanE] = NextEl(Candidate) THEN Counter + 1 ELSE IF Counter = 0 THEN 0 ELSE Counter - 1
    /\ UNCHANGED S

Done ==
    /\ ScanE > Len(S)
    /\ UNCHANGED vars

Next == ScanStep \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(ScanStep)

\* Any true majority element must equal the candidate after a full scan.
Correct ==
    /\ ScanE > Len(S)
    /\ \A e \in Values : (Cardinality({i \in 1..Len(S) : S[i] = e}) * 2 > Len(S)) => e = Candidate

\* The counter is only positive when the candidate is grounded at the current
\* scan position, and a zero counter leaves the candidate free to change.
Inv ==
    /\ (Counter > 0) => (Candidate = S[ScanE])
    /\ (Counter = 0) => TRUE

\* BoundedSeq replaces Seq in the model checking configuration, so no extra
\* declaration of Seq is needed here; it is never used directly.
====