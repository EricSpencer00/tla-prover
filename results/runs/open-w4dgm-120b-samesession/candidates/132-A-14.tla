---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

(* Reference model: a finitary configuration of the Boyer-Moore majority vote     *)
(* algorithm, with all sequences up to a bounded length drawn from three distinct  *)
(* model values.  The bounded-sequence operator below replaces Seq so the state    *)
(* space stays finite.                                                             *)

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq is a finitary stand-in for Seq, ranging over all functions whose  *)
\* length stays within the checkable bound.                                    \* 
BoundedSeq == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, scanPos, cand, cnt

vars == <<seq, scanPos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ scanPos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ scanPos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  IF scanPos <= Len(seq) THEN
    \/ LET x == seq[scanPos] IN
         IF cnt = 0 THEN /\ cand' = x
                       /\ cnt' = 1
         ELSE IF x = cand THEN /\ cnt' = cnt + 1
                             /\ UNCHANGED cand
         ELSE /\ cnt' = cnt - 1
              /\ UNCHANGED cand
    /\ scanPos' = scanPos + 1
    /\ seq' = seq
  ELSE UNCHANGED vars

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

(* Reclaimed majority vote correctness: a true majority element must survive   *)
(* the scan as the candidate once the scan completes.                         *)
Correct ==
  (scanPos = Len(seq) + 1 /\ \E c \in Values : c # cand /\ 2 * Count(seq, c) > Len(seq))
    => (2 * Count(seq, cand) > Len(seq))

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Inv == \A i \in 1..Len(seq) : seq[i] \in Values

Properties == Spec /\ Correct

====