---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, C, bound

(*--- value domain ---*)
ValueSet == { A, B, C }

(*--- bounded sequences over the value domain ---*)
BoundedSeq == { s \in Seq(ValueSet) : Len(s) <= bound }

(*--- state variables ---*)
VARIABLES seq, i, cand, cnt

(*--- initial state ---*)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

(*--- one scanning step ---*)
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt'  = 1
         ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(*--- stutter when the scan is finished ---*)
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED << seq, i, cand, cnt >>

Next == Scan \/ Done

(*--- specification ---*)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*--- type correctness invariant ---*)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(*--- majority predicate for a given value ---*)
Majority(v) ==
    LET cntV == Cardinality({ j \in 1..Len(seq) : seq[j] = v })
    IN cntV > Len(seq) \div 2

(*--- safety property: any true majority must equal the final candidate ---*)
Correct ==
    \A v \in ValueSet :
        (Majority(v) => (i > Len(seq) /\ cand = v))

(*--- inductive invariant (example) ---*)
Inv ==
    /\ cnt >= 0
    /\ cand \in ValueSet

====