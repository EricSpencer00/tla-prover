---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

(* ------------------------------------------------------------------------- *)
(*  The set of possible values (the three distinct elements)                  *)
(* ------------------------------------------------------------------------- *)
Values == {A, B, C}

(* ------------------------------------------------------------------------- *)
(*  Bounded sequences: Seq is the set of all sequences over Values whose     *)
(*  length is at most the natural number bound.                               *)
(* ------------------------------------------------------------------------- *)
BoundedSequences == { s \in Seq(Values) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* ------------------------------------------------------------------------- *)
(*  Helper definitions                                                      *)
(* ------------------------------------------------------------------------- *)
SeqNext == 
  IF i < Len(seq) THEN i + 1
  ELSE i

(* ------------------------------------------------------------------------- *)
(*  Initial state (Init)                                                    *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ seq \in BoundedSequences
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

(* ------------------------------------------------------------------------- *)
(*  Next-state relation (Next)                                              *)
(* ------------------------------------------------------------------------- *)
Next ==
  /\ i <= Len(seq)                                    \* only if not finished
  /\ LET x == seq[i] IN
       IF i > Len(seq) THEN
         /\ UNCHANGED <<seq, i, cand, cnt>>
       ELSE IF cnt = 0 THEN
         /\ cand' = x
         /\ cnt'  = 1
         /\ i'    = i + 1
         /\ UNCHANGED seq
       ELSE IF cand = x THEN
         /\ cnt' = cnt + 1
         /\ i'   = i + 1
         /\ UNCHANGED <<seq, cand>>
       ELSE
         /\ cnt' = cnt - 1
         /\ i'   = i + 1
         /\ UNCHANGED <<seq, cand>>

(* ------------------------------------------------------------------------- *)
(*  Specification (Spec)                                                    *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* ------------------------------------------------------------------------- *)
(*  Type invariants (TypeOK)                                                *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
  /\ seq \in BoundedSequences
  /\ i \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

(* ------------------------------------------------------------------------- *)
(*  Safety invariant: after a complete scan, if there is a true majority    *)
(*  element in the original sequence, it must equal the final candidate.   *)
(* ------------------------------------------------------------------------- *)
Correct ==
  /\ i > Len(seq)                                    \* scan finished
  /\ \A v \in Values :
        (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2)
        => v = cand

(* ------------------------------------------------------------------------- *)
(*  Inductive invariant (Inv) – a stronger property that holds at all times *)
(* ------------------------------------------------------------------------- *)
Inv ==
  /\ i \in 1..(Len(seq) + 1)
  /\ (cnt = 0) => cand \in Values
  /\ (cnt > 0) => cand \in Values

=============================================================================