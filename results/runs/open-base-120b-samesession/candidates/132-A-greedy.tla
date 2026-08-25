---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* The set of possible element values *)
Values == {A, B, C}

(* All sequences (functions) of length 0..bound over Values *)
BoundedSeq == { s : \E n \in 0..bound : s \in [1..n -> Values] }

VARIABLES seq, i, cand, cnt

(* Length of the current sequence *)
SeqLen == Len(seq)

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(* One step of the Boyer‑Moore scan *)
Next ==
    \/ /\ i <= SeqLen
       /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
              /\ i'    = i + 1
          ELSE IF x = cand THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
              /\ i'    = i + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
              /\ i'    = i + 1
    \/ /\ i > SeqLen
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Full specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(* Helper: number of occurrences of v in seq *)
Count(v) == Cardinality({ j \in 1..SeqLen : seq[j] = v })

(* Correctness invariant: any majority element must equal the final candidate *)
Correct ==
    (i > SeqLen) => ( \A v \in Values : (Count(v) > SeqLen / 2) => cand = v )

(* Simple inductive invariant *)
Inv ==
    /\ i \in 1..(SeqLen + 1)
    /\ cnt \in Nat

====