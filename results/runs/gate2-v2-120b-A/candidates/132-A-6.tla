---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound, Seq

(* The set of possible element values *)
Vals == {A, B, C}

(* Helper: all sequences (functions) from 1..n to Vals, for 0 <= n <= bound *)
AllSeqs == { s \in [1..n -> Vals] : n \in 0..bound }

(* Variables *)
VARIABLES seq, i, cand, cnt

(* State predicate for a valid sequence *)
SeqValid(s) == 
    /\ s \in [1..Len(s) -> Vals]
    /\ Len(s) <= bound

(* Initial state *)
Init ==
    /\ seq \in AllSeqs
    /\ i = 1
    /\ cnt = 0
    /\ cand \in Vals

(* Scan action *)
Next ==
    \/ /\ i <= Len(seq)               \* we have an element to scan
       /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF x = cand THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)                \* already past the end, stutter
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in AllSeqs
    /\ i \in Nat
    /\ cand \in Vals
    /\ cnt \in Nat

(* Majority-candidate correctness invariant *)
Correct ==
    /\ i > Len(seq)      \* scan complete
    => 
       ( \A v \in Vals :
            (Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2)
            => v = cand)

(* Inductive invariant, same as Correct together with TypeOK *)
Inv == TypeOK /\ Correct

=============================================================================