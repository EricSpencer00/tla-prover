---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible element values *)
Values == { A, B, C }

(* Finite sequences of length up to ''bound'' over ''Values'' *)
BoundedSeq == UNION { [1..n -> Values] : n \in 0..bound }

(* Length of a (possibly empty) sequence *)
Len(s) == IF s = {} THEN 0 ELSE Max(DOMAIN s)

VARIABLES seq, i, cand, cnt

(* Type correctness invariant *)
TypeOK == /\ seq \in BoundedSeq
          /\ i \in Nat
          /\ cand \in Values
          /\ cnt \in Nat

(* Initial state *)
Init == /\ seq \in BoundedSeq
        /\ i = 1
        /\ cnt = 0
        /\ cand \in Values

(* Scan the next element while the scan is not finished *)
Scan ==
  /\ i <= Len(seq)
  /\ LET x == seq[i] IN
     IF cnt = 0 THEN
        /\ cand' = x
        /\ cnt' = 1
        /\ i' = i + 1
     ELSE IF x = cand THEN
        /\ cnt' = cnt + 1
        /\ cand' = cand
        /\ i' = i + 1
     ELSE
        /\ cnt' = cnt - 1
        /\ cand' = cand
        /\ i' = i + 1

(* Stutter when the scan has completed *)
Done ==
  /\ i > Len(seq)
  /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

(* The overall specification *)
Spec ==
  Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

(* Inductive invariant *)
Inv ==
  /\ cnt \in Nat
  /\ i \in 1..Len(seq)+1
  /\ cand \in Values

(* Definition of a majority element in the current sequence *)
Majority(v) ==
  \E n \in 0..bound :
    /\ seq \in [1..n -> Values]
    /\ Cardinality({ j \in 1..n : seq[j] = v }) > n / 2

(* Correctness property: after a complete scan, any true majority must equal the candidate *)
Correct ==
  /\ i > Len(seq)
  /\ \A v \in Values : (Majority(v) => cand = v)

====