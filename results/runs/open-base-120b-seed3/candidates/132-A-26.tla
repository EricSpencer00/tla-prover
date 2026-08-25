---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

(* --- Value domain --- *)
ValueSet == { A, B, C }

(* --- Finite sequences over ValueSet up to length bound --- *)
BoundedSeq == { s \in Seq(ValueSet) : Len(s) <= bound }

(* --- State variables --- *)
VARIABLES seq, i, cand, cnt

(* --- Initial state --- *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ValueSet

(* --- One scan step --- *)
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
          \/ /\ cnt = 0
             /\ cand' = x
             /\ cnt' = 1
          \/ /\ cnt # 0 /\ cand = x
             /\ cand' = cand
             /\ cnt' = cnt + 1
          \/ /\ cnt # 0 /\ cand # x
             /\ cand' = cand
             /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(* --- Next-state relation --- *)
Next ==
    \/ Scan
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* --- Specification --- *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* --- Type correctness invariant --- *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* --- Set of majority elements (if any) --- *)
MajoritySet ==
    { x \in ValueSet :
        Cardinality({ j \in 1..Len(seq) : seq[j] = x }) > Len(seq) / 2 }

(* --- Correctness property: after a complete scan, any true majority must equal the candidate --- *)
Correct ==
    (i > Len(seq)) =>
        \A x \in ValueSet :
            ( Cardinality({ j \in 1..Len(seq) : seq[j] = x }) > Len(seq) / 2 )
            => cand = x

(* --- Inductive invariant used in the Boyer‑Moore algorithm --- *)
Inv ==
    /\ i \in 1..(Len(seq) + 1)
    /\ (cnt = 0) \/ (cnt = 2 * Cardinality({ j \in 1..(i-1) : seq[j] = cand }) - (i-1))

====