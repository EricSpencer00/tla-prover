---- MODULE MCMajority ---------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

(* The universe of values that can appear in the sequences. *)
Value == {A, B, C}

(* BoundedSeq(Value) is the set of all finite sequences (including the empty *)
(* sequence) whose elements are drawn from Value and whose length does not   *)
(* exceed the constant bound.                                                *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The majority vote algorithm, taken from the imported Majority module.   *)
Init ==
  /\ seq \in BoundedSeq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  \/ /\ i <= Len(seq)
        /\ IF cnt = 0
              THEN /\ cand' = seq[i]
                   /\ cnt' = 1
              ELSE IF cand = seq[i]
                      THEN /\ cand' = cand
                           /\ cnt' = cnt + 1
                      ELSE /\ cand' = cand
                           /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED <<seq>>
  \/ /\ i > Len(seq)
        /\ UNCHANGED <<seq, i, cand, cnt>>

(* The invariant that the Majority module expects: after processing the
   whole sequence, if a value occurs more than half the time, it must be the
   current candidate. *)
MajorityInv ==
  (i > Len(seq)) => 
    (\A v \in Value :
        (Cardinality({j \in 1..Len(seq) : seq[j] = v}) >
         Len(seq) / 2) => v = cand)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================