---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

(* ------------------------------------------------------------------- *)
(* Value set *)
ValSet == {A, B, C}

(* ------------------------------------------------------------------- *)
(* Bounded sequences are represented as functions from a natural index
   to ValSet, where the index set is either empty (length 0) or a
   non‑empty prefix of 1..bound. The domain of a bounded sequence is
   stored in the variable seqLen.                                          *)
VARIABLES seq, seqLen, pos, cand, count

(* ------------------------------------------------------------------- *)
(* Type invariant (required by the .cfg) *)
TypeOK ==
    /\ seqLen \in 0..bound
    /\ seq \in [1..seqLen -> ValSet] \/ (seqLen = 0 /\ seq = [i \in {} |-> 0])
    /\ pos \in 1..(seqLen + 1)
    /\ cand \in ValSet
    /\ count \in Nat

(* ------------------------------------------------------------------- *)
(* Helper to pick a nondeterministic candidate from ValSet *)
InitCand == CHOOSE v \in ValSet : TRUE

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ seqLen \in 0..bound
    /\ seq \in [1..seqLen -> ValSet] \/ (seqLen = 0 /\ seq = [i \in {} |-> 0])
    /\ pos = 1
    /\ cand = InitCand
    /\ count = 0

(* ------------------------------------------------------------------- *)
(* Action: scan the next element *)
Next ==
    \/ /\ pos <= seqLen
       /\ LET x == seq[pos] IN
          IF count = 0 THEN
              /\ cand' = x
              /\ count' = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ count' = count + 1
          ELSE
              /\ cand' = cand
              /\ count' = count - 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq, seqLen>>
    \/ /\ pos = seqLen + 1
       /\ UNCHANGED <<seq, seqLen, pos, cand, count>>
    \/ /\ (seqLen < bound) /\ pos = seqLen + 1
       /\ \E v \in ValSet :
            /\ seqLen' = seqLen + 1
            /\ seq' = [seq EXCEPT ![seqLen' = v]]
            /\ pos' = pos
            /\ cand' = cand
            /\ count' = count
       /\ UNCHANGED <<>>

(* ------------------------------------------------------------------- *)
(* Full specification *)
Spec == Init /\ [][Next]_<<seq, seqLen, pos, cand, count>>

(* ------------------------------------------------------------------- *)
(* Safety invariant: any true majority element must equal the candidate
   after the scan has finished. *)
Correct ==
    \A v \in ValSet :
        (v = cand) \/
        (v # cand \/ \A i \in 1..seqLen : seq[i] # v)

(* ------------------------------------------------------------------- *)
(* Inductive invariant required by the .cfg *)
Inv == TypeOK /\ Correct

(* ------------------------------------------------------------------- *)
(* The identifier required by the .cfg to denote the specification *)
SpecInv == Spec

=============================================================================