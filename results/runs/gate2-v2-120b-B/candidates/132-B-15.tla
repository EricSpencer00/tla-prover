------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* bound must be a natural number (including zero) *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(***************************************************************************)
(* Majority algorithm (Boyer–Moore)                                         *)
(***************************************************************************)

Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cnt = 0
    /\ cand = CHOOSE v \in Value : TRUE \* arbitrary element of Value

Next ==
    /\ i \le Len(seq)
    /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt'  = 1
          ELSE IF seq[i] = cand
               THEN /\ cand' = cand
                    /\ cnt'  = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(***************************************************************************)
(* Safety invariant: cand always belongs to Value                        *)
(***************************************************************************)

CandInValue == cand \in Value

=============================================================================