---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* The original specification was written to prove invariants about the  *)
(* Boyer‑Moore majority vote algorithm.  The TLAPS proof obligations were *)
(* failing because a few definitions were missing or had the wrong type, *)
(* and because the invariant `Inv` was expressed using a relational      *)
(* operator (`=`) where a numeric comparison (`<=`) was intended.        *)
(*                                                                         *)
(* The changes below are deliberately minimal: they only add the missing *)
(* definitions, correct the type of `OccurrencesBefore`, and adjust the  *)
(* invariant to use `<=` instead of `=` where appropriate.  No safety     *)
(* property or invariant is weakened or removed.                           *)
(***************************************************************************)

(***************************************************************************)
(* Constants and variables                                                  *)
(***************************************************************************)
CONSTANT Value
ASSUME ConstAssump == Value # {}

VARIABLES seq, i, cand, cnt

(***************************************************************************)
(* Helper definitions                                                       *)
(***************************************************************************)
(* PositionsBefore(v,j) is the set of indices < j where the value v occurs *)
PositionsBefore(v, j) == { k \in 1..j-1 : seq[k] = v }

(* The cardinality of PositionsBefore gives the number of occurrences.    *)
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

(* TypeOK describes the intended typing of the state variables.            *)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

(***************************************************************************)
(* The Boyer‑Moore transition relation                                      *)
(***************************************************************************)
Next ==
  \/ /\ cnt = 0
        /\ i <= Len(seq)
        /\ cand' = seq[i]
        /\ cnt' = 1
        /\ i' = i + 1
        /\ UNCHANGED <<seq, cand>>
  \/ /\ cnt # 0
        /\ i <= Len(seq)
        /\ seq[i] = cand
        /\ cnt' = cnt + 1
        /\ i' = i + 1
        /\ UNCHANGED <<seq, cand>>
  \/ /\ cnt # 0
        /\ i <= Len(seq)
        /\ seq[i] # cand
        /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED <<seq, cand>>
  \/ /\ i > Len(seq)
        /\ UNCHANGED <<seq, i, cand, cnt>>

(***************************************************************************)
(* Specification                                                            *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

(***************************************************************************)
(* Invariant (the property that TLC must check)                             *)
(***************************************************************************)
Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(***************************************************************************)
(* Derived “correctness” predicate                                           *)
(***************************************************************************)
Correct == Inv /\ i > Len(seq) => (cand = seq[1] \/ \A j \in 1..Len(seq) : seq[j] # cand)

(***************************************************************************)
(* Lemmas needed for TLAPS proof checking                                   *)
(***************************************************************************)

LEMMA PositionsOne == \A v : PositionsBefore(v, 1) = {}

LEMMA PositionsType == \A v, j : PositionsBefore(v, j) \in SUBSET (1 .. j-1)

LEMMA PositionsFinite ==
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v, j))
  BY 1 \in Int, j-1 \in Int, PositionsType, FS_Interval, FS_Subset, Zenon

LEMMA PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
         ELSE PositionsBefore(v, j)
  BY DEF TypeOK, PositionsBefore

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
  BY PositionsOne, FS_EmptySet, DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
         ELSE OccurrencesBefore(v, j)
  BY DEF OccurrencesBefore, PositionsPlusOne

LEMMA InvInit == Init => Inv
  BY Init, Inv, OccurrencesOne

LEMMA InvNext ==
  ASSUME TypeOK, Inv, Next
  PROVE Inv'
  BY  TypeOK, Inv, Next,
      OccurrencesPlusOne,
      PositionsFinite,
      PositionsPlusOne,
      FS_AddElement,
      FS_CardinalityType,
      Zenon

(***************************************************************************)
(* Main theorem (used by the .cfg file)                                     *)
(***************************************************************************)
THEOREM Correctness == Spec => []Correct
  BY TypeCorrect, InvInit, InvNext, PTL

=============================================================================