---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound, Seq

(* --algorithm MajorityVote
variables
    seq   \in Seq,
    i     \in 1..bound,
    cand  \in {A, B, C},
    cnt   \in Nat

variables
    prevCnt \in Nat

define
    InitSeq(s) == s \in Seq
end define;

Init ==
    /\ \E s \in Seq :
          /\ seq = s
          /\ i = 1
          /\ cand \in {A, B, C}
          /\ cnt = 0

Next ==
    \/ ScanNext
    \/ ScanDone

ScanNext ==
    /\ i <= Len(seq)
    /\ IF cnt = 0 THEN
          /\ cand' = seq[i]
          /\ cnt' = 1
       ELSE IF cand = seq[i] THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
       ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq>>

ScanDone ==
    /\ i > Len(seq)
    /\ cand' = cand
    /\ cnt' = cnt
    /\ i' = i
    /\ UNCHANGED <<seq>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

TypeOK ==
    /\ seq \in Seq
    /\ i \in 1..bound
    /\ cand \in {A, B, C}
    /\ cnt \in Nat

Inv ==
    /\ TypeOK
    /\ (i > Len(seq) => cand \in {A, B, C})

Correct ==
    /\ i > Len(seq)
    /\ \E v \in {A, B, C} :
          ( \A j \in DOMAIN seq : seq[j] = v )
          => cand = v

=============================================================================