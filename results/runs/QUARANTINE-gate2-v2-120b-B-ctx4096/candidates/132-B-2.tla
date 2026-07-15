---- MODULE MCMajority ---------------------------------
EXTENDS Integers, Sequences
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand = A
    /\ cnt = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \o << Value[1 + i \bmod 3] >>
       /\ cand' = cand
       /\ cnt' = cnt
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

CandidateIsMajority ==
    /\ \E n \in Nat :
          n <= Len(seq) /\ 
          \E m \in 0 .. n :
               /\ \A j \in 1 .. n :
                      (seq[j] = cand) => (j <= m)
               /\ \A j \in 1 .. n :
                      (seq[j] # cand) => (j > m)

\* Minimal invariant ensuring the candidate variable is always one of the three values
CandidateRange ==
    cand \in Value

THEOREM Spec => []CandidateRange

====