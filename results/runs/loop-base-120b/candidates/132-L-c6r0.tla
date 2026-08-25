---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

(*--- value domain ---------------------------------------------------*)
Values == { A, B, C }

(*--- finite sequences up to the given bound --------------------------*)
ASSUME bound \in Nat
BoundedSeq == { s \in Seq : Len(s) \in 0..bound }

(*--- state variables ------------------------------------------------*)
VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(*--- initialization -------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*--- next‑state relation --------------------------------------------*)
Next ==
    \/ Scan
    \/ Stutter

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

Stutter ==
    /\ i > Len(seq)
    /\ UNCHANGED << seq, i, cand, cnt >>

(*--- specification ---------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--- invariants ------------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Count(s, v) ==
    Cardinality({ j \in 1..Len(s) : s[j] = v })

Correct ==
    /\ i > Len(seq)                \* scan has finished
    /\ \A v \in Values :
          (Count(seq, v) > Len(seq) / 2) => cand = v

Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in Values)

====