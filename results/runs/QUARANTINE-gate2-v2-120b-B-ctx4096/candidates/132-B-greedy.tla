---- MODULE MCMajority ----------------------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* All sequences over Value whose length does not exceed bound. *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The majority algorithm from the imported module. *)
Majority(seq, i, cand, cnt) ==
  /\ i = Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

(* Initial state: empty sequence, start index 1, no candidate, zero count. *)
Init ==
  /\ seq = <<>>
  /\ i = 1
  /\ cand = A          \* any element of Value; choice does not affect correctness
  /\ cnt = 0

(* One step of the algorithm, processing the next element of seq. *)
Next ==
  \/ /\ i <= Len(seq)
        /\ LET x == seq[i] IN
           IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
           ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
           ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED seq
  \/ /\ i > Len(seq)          \* after processing all elements, stay idle
        /\ UNCHANGED <<seq, i, cand, cnt>>

(* Safety invariant: if a value occurs more than half the length of the
   sequence, it must be the current candidate. *)
MajorityInv ==
  \A v \in Value :
    (2 * Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq))
    => v = cand

(* Liveness property (optional, not used for safety checking). *)
EventuallyCorrect ==
  <> (cnt = 0 \/ (cnt > 0 /\ cand \in Value))

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================