---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

ASSUME bound \in Nat
ASSUME A # B /\ B # C /\ A # C

(* Finite sequences of length at most bound over a set V. *)
BoundedSeq(V) ==
  { s : \E n \in 0..bound : s \in [1..n -> V] }

VARIABLES seq, i, cand, count

(* Length of a (possibly empty) sequence. *)
SeqLen(s) == IF DOMAIN s = {} THEN 0 ELSE Max(DOMAIN s)

Init ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i = 1
  /\ cand \in {A, B, C}
  /\ count = 0

IsComplete == i = SeqLen(seq) + 1

Scan ==
  /\ i <= SeqLen(seq)
  /\ LET x == seq[i] IN
       IF count = 0 THEN
         /\ cand' = x
         /\ count' = 1
       ELSE IF cand = x THEN
         /\ count' = count + 1
       ELSE
         /\ count' = count - 1
       /\ i' = i + 1
  /\ UNCHANGED seq

Next ==
  \/ Scan
  \/ UNCHANGED <<seq, i, cand, count>>

Spec ==
  Init /\ [][Next]_<<seq, i, cand, count>> /\ WF_<<seq, i, cand, count>>(Scan)

(* -------------------------------------------------------------------------
   Invariants required by the .cfg file
   ------------------------------------------------------------------------- *)

TypeOK ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ i \in Nat
  /\ cand \in {A, B, C}
  /\ count \in Nat
  /\ i <= SeqLen(seq) + 1

CountOcc(v) == Cardinality({ j \in DOMAIN seq : seq[j] = v })

Correct ==
  IsComplete => 
    \A v \in {A, B, C} :
      (CountOcc(v) > SeqLen(seq) / 2) => cand = v

Inv ==
  /\ count >= 0
  /\ i >= 1 /\ i <= SeqLen(seq) + 1

====