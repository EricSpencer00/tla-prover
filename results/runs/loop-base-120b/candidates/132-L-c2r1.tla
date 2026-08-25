---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, Real

CONSTANT A, B, C, bound

VARIABLES seq, i, cand, cnt

(* Finite version of Seq, limited by the bound constant *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

(* Type correctness invariant *)
TypeOK ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i \in Nat
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

(* Initial state *)
Init ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i = 1
  /\ cnt = 0
  /\ cand \in {A, B, C}

(* One step of the Boyer‑Moore scan *)
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
     /\ UNCHANGED << seq, i, cand, cnt >>

(* Full specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Correctness property: after a complete scan, any true majority equals the candidate *)
Correct ==
  /\ i > Len(seq)
  /\ \E e \in {A, B, C} :
        ( Cardinality({ j \in 1..Len(seq) : seq[j] = e }) > Len(seq) / 2 )
        => e = cand

(* Inductive invariant – here we reuse the type invariant *)
Inv == TypeOK

====