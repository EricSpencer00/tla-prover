---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible element values *)
ValueSet == { A, B, C }

(* BoundedSeq replaces Seq from Sequences; it limits the length of sequences. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

(* Scan the next element according to the Boyer‑Moore algorithm *)
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        /\ IF cnt = 0 THEN
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

(* Overall next-state relation *)
Next ==
    \/ Scan
    \/ /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

(* Specification *)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* Inductive invariant: relationship between cnt and the processed prefix *)
Inv ==
    /\ cnt >= 0
    /\ cnt =
        Cardinality({ i \in 1..pos-1 : seq[i] = cand })
        -
        Cardinality({ i \in 1..pos-1 : seq[i] # cand })

(* Correctness property: any true majority must equal the final candidate *)
Correct ==
    /\ pos > Len(seq)
    => \A m \in ValueSet :
          ( Cardinality({ i \in 1..Len(seq) : seq[i] = m }) > Len(seq) / 2 )
          => m = cand

====