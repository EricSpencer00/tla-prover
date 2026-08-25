---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible element values *)
ValueSet == { A, B, C }

(* All sequences over ValueSet whose length is at most bound *)
BoundedSeq == UNION { [1..n -> ValueSet] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in ValueSet

(* One step of the Boyer‑Moore scan *)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

(* Full specification *)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* Definition of a majority element in the current sequence *)
Majority(e) ==
    /\ e \in ValueSet
    /\ Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq) / 2

(* Scan has finished *)
Complete == pos > Len(seq)

(* Main correctness property: any true majority must equal the final candidate *)
Correct ==
    Complete => (\A e \in ValueSet : Majority(e) => e = cand)

(* Inductive invariant – here we reuse the type invariant *)
Inv == TypeOK
====