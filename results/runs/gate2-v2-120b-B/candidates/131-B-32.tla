---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The following lemmas are needed only for the proof of the main          *)
(* invariant.  They are deliberately kept minimal and do not change the    *)
(* behaviour of the specification.                                         *)
(***************************************************************************)

(* PositionsBefore(v,j) is the set of indices < j where the sequence entry  *)
(* equals v.                                                               *)
PositionsBefore(v, j) == 
  { k \in 1..j-1 : seq[k] = v }

(* OccurrencesBefore(v,j) is the number of times v appears before position j.*)
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

(***************************************************************************)
(* Utility lemmas about PositionsBefore and OccurrencesBefore.             *)
(***************************************************************************)

LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}
BY DEF PositionsBefore

LEMMA PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)
BY DEF PositionsBefore

LEMMA PositionsFinite == 
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v,j))
BY 1 \in Int, j-1 \in Int, PositionsType, FS_Interval, FS_Subset, Zenon

LEMMA PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v,j) \cup {j}
         ELSE PositionsBefore(v,j)
BY DEF TypeOK, PositionsBefore, SeqCat, SeqAdd

LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat
BY PositionsFinite, FS_CardinalityType, DEF OccurrencesBefore

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet, DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
PROOF
  BY DEF OccurrencesBefore, PositionsPlusOne, FS_CardinalityAdd

(***************************************************************************)
(* Invariant and correctness definitions                                  *)
(***************************************************************************)

VARIABLES seq, i, cand, cnt

(* Type correctness: the variables always respect their intended domains. *)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

(* The inductive invariant used in the classic Boyer‑Moore majority algorithm. *)
Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(* When the algorithm finishes, the invariant implies the majority property. *)
Correct ==
  \/ Len(seq) = 0
  \/ \E cand \in Value :
        /\ cnt = OccurrencesBefore(cand, Len(seq) + 1)
        /\ 2 * cnt > Len(seq)

(* Initial state. *)
Init ==
  /\ seq = <<>>
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0
  /\ Inv
  /\ TypeOK

(* One step of the Boyer‑Moore algorithm. *)
Next ==
  /\ i <= Len(seq)
  /\ \/ /\ cnt = 0
        /\ cand' = seq[i]
        /\ cnt' = 1
     \/ /\ cnt # 0 /\ seq[i] = cand
        /\ cand' = cand
        /\ cnt' = cnt + 1
     \/ /\ cnt # 0 /\ seq[i] # cand
        /\ cand' = cand
        /\ cnt' = cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED << seq, cand, cnt >>

(* Full specification. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================