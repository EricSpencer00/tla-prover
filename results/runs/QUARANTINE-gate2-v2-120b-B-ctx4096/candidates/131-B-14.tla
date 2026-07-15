---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Helper definitions (unchanged from the original specification)          *)
(***************************************************************************)

POSITIONS == PositionsBefore

OCCURRENCES == OccurrencesBefore

(***************************************************************************)
(* lemmata about PositionsBefore and OccurrencesBefore                    *)
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
  BY DEF PositionsBefore, TypeOK

LEMMA OccurrencesType ==
  \A v, j : OccurrencesBefore(v,j) \in Nat
  BY DEF OccurrencesBefore, PositionsFinite, FS_Cardinality

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
  BY DEF OccurrencesBefore, PositionsOne

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
  BY DEF OccurrencesBefore, PositionsPlusOne

(***************************************************************************)
(* The main invariant and correctness statement                           *)
(***************************************************************************)

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Correct ==
  \/ i = Len(seq) + 1
  \/ (cnt > 0 /\ 2 * (OccurrencesBefore(cand, Len(seq)) - cnt) <= Len(seq) - cnt)

=============================================================================