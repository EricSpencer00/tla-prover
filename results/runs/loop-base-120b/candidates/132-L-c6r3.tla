---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

(*--- value domain ---------------------------------------------------*)
Values == { A, B, C }

(*--- bounded sequences up to the given bound --------------------------*)
(* Restrict sequences to those whose length is at most 'bound'. *)
ASSUME bound \in Nat

SeqOfLen(n, S) == { s \in Seq(S) : Len(s) = n }

BoundedSeq(S) == UNION { SeqOfLen(n, S) : n \in 0..bound }

(*--- state variables ------------------------------------------------*)
VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(*--- helper definitions ---------------------------------------------*)
Count(s, v) ==
    Cardinality({ j \in 1..Len(s) : s[j] = v })

(*--- type invariant -------------------------------------------------*)
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*--- initialization -------------------------------------------------*)
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*--- actions --------------------------------------------------------*)
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

Next ==
    Scan \/ Stutter

(*--- specification ---------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--- safety properties ----------------------------------------------*)
Correct ==
    /\ i > Len(seq)                \* scan has finished
    /\ \A v \in Values :
          (2 * Count(seq, v) > Len(seq)) => cand = v

Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in Values)

====