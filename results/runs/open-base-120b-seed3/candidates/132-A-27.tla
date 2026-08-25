---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

ValueSet == { A, B, C }

(* Bounded sequence operator: replaces Seq with a finite version *)
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

Init ==
   /\ seq \in BoundedSeq(ValueSet)
   /\ i = 1
   /\ cnt = 0
   /\ cand \in ValueSet

Next ==
   \/ (* scan the next element *)
      /\ i <= Len(seq)
      /\ LET x == seq[i] IN
         \/ /\ cnt = 0
            /\ cand' = x
            /\ cnt' = 1
         \/ /\ cnt > 0 /\ cand = x
            /\ cand' = cand
            /\ cnt' = cnt + 1
         \/ /\ cnt > 0 /\ cand # x
            /\ cand' = cand
            /\ cnt' = cnt - 1
      /\ i' = i + 1
   \/ (* stutter after the scan is complete *)
      /\ i > Len(seq)
      /\ UNCHANGED << seq, i, cand, cnt >>

Spec == Init /\ [][Next]_<< seq, i, cand, cnt >>

TypeOK ==
   /\ seq \in BoundedSeq(ValueSet)
   /\ i \in Nat
   /\ cnt \in Nat
   /\ cand \in ValueSet

MajCount(v) == Cardinality({ j \in 1..Len(seq) : seq[j] = v })

Correct ==
   /\ i > Len(seq)
   => \A v \in ValueSet :
        (MajCount(v) > Len(seq) / 2) => cand = v

Inv ==
   /\ cnt >= 0
   /\ (cnt = 0 => cand \in ValueSet)
   /\ (cnt > 0 => cand \in ValueSet)

====