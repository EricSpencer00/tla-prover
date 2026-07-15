---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------*)
(*  Constants                                                       *)
(*--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------*)
(*  Main specification (imported or redefined for completeness)      *)
(*--------------------------------------------------------------------*)
VARIABLES seq, cand, cnt, i, out

(* seq is the input sequence of values, indexed from 1 to Len(seq) *)
(* cand is the current candidate for majority *)
(* cnt  is the current counter associated with cand *)
(* i    is the index of the next element to process (1..Len(seq)+1) *)
(* out  is the output after the whole sequence has been processed *)

(* Domain of seq: each element must be a Value *)
SeqDomain == 1 .. Len(seq)

(* Type of each variable *)
VARIABLE_TYPE ==
  /\ i \in Nat
  /\ cand \in Value
  /\ cnt \in Nat
  /\ out \in Value
  /\ seq \in [SeqDomain -> Value]

(* Initial state: start before processing any element *)
Init ==
  /\ i = 1
  /\ cand = DefaultValue
  /\ cnt = 0
  /\ out = DefaultValue
  /\ \A j \in SeqDomain: seq[j] \in Value

(* The main step of the Boyer-Moore algorithm *)
Next ==
  \/ /\ i <= Len(seq)
        /\ LET x == seq[i] IN
           IF cnt = 0 THEN
               /\ cand' = x
               /\ cnt' = 1
           ELSE
               IF x = cand THEN
                   /\ cnt' = cnt + 1
               ELSE
                   /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED <<seq, out>>
  \/ /\ i = Len(seq) + 1
        /\ out' = cand
        /\ UNCHANGED <<seq, cand, cnt, i>>

Spec ==
  Init /\ [][Next]_<<i, cand, cnt, out, seq>>

(*--------------------------------------------------------------------*)
(*  Invariant definitions                                            *)
(*--------------------------------------------------------------------*)
(* Type correctness invariant *)
TypeOK ==
  /\ i \in Nat
  /\ cand \in Value
  /\ cnt \in Nat
  /\ out \in Value
  /\ seq \in [SeqDomain -> Value]

(* The inductive invariant from the original spec (re‑expressed here) *)
Inv ==
  /\ i \in 1 .. Len(seq) + 1
  /\ (cnt = 0 => TRUE)
  /\ (cnt > 0 => cand \in Value)

(* Correctness: after the whole sequence has been processed, any value
   that occurs in a strict majority must be equal to the final output. *)
Correct ==
  /\ i = Len(seq) + 1
  /\ out = cand
  /\ (\A v \in Value :
        (Cardinality({j \in SeqDomain : seq[j] = v}) > Len(seq) / 2) => v = cand)

(*--------------------------------------------------------------------*)
(*  Specification name (required by the .cfg)                        *)
(*--------------------------------------------------------------------*)
Spec == Spec

====