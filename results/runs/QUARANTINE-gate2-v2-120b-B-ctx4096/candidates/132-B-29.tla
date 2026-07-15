---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible vote values *)
Value == {A, B, C}

(* Sequences (functions from 1..n to Value) of length up to 'bound' *)
BoundedSeq == { s \in [1..bound -> Value] : 
                  Len(s) \in 0..bound }

VARIABLES seq, i, cand, cnt

(*--------------------------------------------------------------------
  Majority algorithm (Boyer-Moore majority vote) adapted to bounded
  sequences.
--------------------------------------------------------------------*)

Init ==
    /\ seq \in BoundedSeq          \* any allowed sequence
    /\ i = 1
    /\ cand = A                     \* arbitrary initial candidate
    /\ cnt = 0

Step ==
    \/ /\ i <= Len(seq) 
       /\ \/ /\ cnt = 0
              /\ cand' = seq[i]
              /\ cnt' = 1
          \/ /\ cnt # 0
              /\ IF seq[i] = cand
                    THEN /\ cand' = cand
                         /\ cnt' = cnt + 1
                    ELSE /\ cnt' = cnt - 1
                         /\ cand' = cand
       /\ i' = i + 1
    \/ /\ i > Len(seq) 
       /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Step

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*--------------------------------------------------------------------
  Invariant: when the scan is finished (i > Len(seq)), the variable
  cand holds a value that appears at least as many times as any other
  value in the processed prefix, i.e., it is a majority candidate.
--------------------------------------------------------------------*)
MajorityCandidate ==
    (i > Len(seq)) => 
        \A v \in Value : 
            Cardinality({ j \in 1..Len(seq) : seq[j] = cand }) >=
            Cardinality({ j \in 1..Len(seq) : seq[j] = v })

=============================================================================