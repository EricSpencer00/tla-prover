---- MODULE MCMajority -----------------------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS bound, A, B, C

(* The set of possible vote values *)
Value == {A, B, C}

(* The set of all sequences (including the empty sequence) over Value,
   whose length is at most the constant "bound". *)
BoundedSeq == { s \in Seq(Value) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 0, no candidate, zero count *)
Init ==
    /\ seq = <<>>
    /\ i   = 0
    /\ cand = {}
    /\ cnt   = 0

(* Transition that appends a new vote to the sequence, respecting the bound *)
Append ==
    /\ i < bound
    /\ \E v \in Value :
         /\ seq' = Append(seq, v)
         /\ i'   = i + 1
         /\ IF cnt = 0 THEN
                /\ cand' = v
                /\ cnt'  = 1
            ELSE IF cand = v THEN
                /\ cand' = cand
                /\ cnt'  = cnt + 1
            ELSE
                /\ cand' = cand
                /\ cnt'  = cnt - 1

(* The overall system action: either stay in Init or perform Append *)
Next == Append

(* Safety invariant expressing the classic majority‑vote guarantee:
   - If the count is zero, there is no candidate.
   - If the count is positive, the candidate (if any) appears more than half
     the times in the current sequence. *)
MajorityInv ==
    (cnt = 0 => cand = {}) /\
    (cnt > 0 => /\ cand \in Value
                /\ Cardinality({ j \in 1..Len(seq) : seq[j] = cand }) > Len(seq) \div 2)

(* Type correctness invariant for documentation purposes only;
   it does not constrain the behavior of the system. *)
TypeCorrect ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ i = Len(seq)
    /\ (cnt = 0 => cand = {})
    /\ (cnt > 0 => cand \in Value)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================