---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

VARIABLES seq, i, cand, cnt

(* BoundedSeq replaces the unbounded Seq from Sequences *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

ValueSet == { A, B, C }

Count(s, v) == Cardinality({ j \in 1..Len(s) : s[j] = v })

PrefixCount(v) ==
  IF i = 1 THEN 0
  ELSE Cardinality({ j \in 1..(i-1) : seq[j] = v })

Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i = 1
  /\ cand \in ValueSet
  /\ cnt = 0

Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
          ( \/ /\ cnt = 0
                /\ cand' = x
                /\ cnt' = 1
                /\ i' = i + 1
            \/ /\ cnt # 0 /\ cand = x
                /\ cand' = cand
                /\ cnt' = cnt + 1
                /\ i' = i + 1
            \/ /\ cnt # 0 /\ cand # x
                /\ cand' = cand
                /\ cnt' = cnt - 1
                /\ i' = i + 1 )
  \/ /\ i > Len(seq) /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat

Correct ==
  (i > Len(seq)) => 
    \A v \in ValueSet : (Count(seq, v) > Len(seq) / 2) => cand = v

Inv ==
  /\ cnt = 2 * PrefixCount(cand) - (i - 1)
  /\ cnt >= 0

====