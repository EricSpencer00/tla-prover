---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

(*--- Bounded sequence definition, replaces Seq from Sequences ---*)
BoundedSeq(S) == 
  UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(*--- Initial state ---*)
Init ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

(*--- Next-state relation ---*)
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        /\ IF cnt = 0 THEN
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
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

vars == <<seq, i, cand, cnt>>

(*--- Specification ---*)
Spec == Init /\ [][Next]_vars

(*--- Type correctness invariant ---*)
TypeOK ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i \in Nat
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

(*--- Inductive invariant (example) ---*)
Inv ==
  /\ cnt >= 0
  /\ i <= Len(seq) + 1

(*--- Correctness property: any true majority must equal the final candidate ---*)
Correct ==
  /\ i > Len(seq)
  /\ LET majSet == { x \in {A, B, C} :
                       Cardinality({ j \in 1..Len(seq) : seq[j] = x }) > Len(seq) / 2 }
     IN  ( majSet = {} \/ cand \in majSet )

====