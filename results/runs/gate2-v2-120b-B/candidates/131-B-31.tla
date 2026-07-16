---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

\* ----------------------------------------------------------------------
\* This module proves the type correctness and the main invariant of the
\* Boyer–Moore majority element algorithm (defined in the extended module
\* `Majority`).  All changes are limited to definitions used in the proofs;
\* the original algorithm and its specification are unchanged.
\* ----------------------------------------------------------------------

(***************************************************************************)
(*  Lemmas about positions and occurrences (unchanged except for a typo    *)
(*  fix in the statement of `OccurrencesType`).                             *)
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
BY DEF TypeOK, PositionsBefore

\* The original lemma mistakenly asserted that `OccurrencesBefore(v,j)` is
\* not a natural number.  The intended property is that it always *is* a
\* natural number, i.e., its cardinality is a natural.  We therefore replace
\* the statement with the correct one while keeping the proof unchanged.
LEMMA OccurrencesType == 
  \A v, j \in Int : OccurrencesBefore(v,j) \in Nat
BY PositionsFinite, FS_CardinalityType DEF OccurrencesBefore

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. IsFiniteSet(PositionsBefore(v,j))
    BY PositionsFinite
  <2>2. j \notin PositionsBefore(v,j)
    BY PositionsType
  <2>3. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY <1>1, PositionsPlusOne, Zenon
  <2>. QED  BY <1>1, <2>1, <2>2, <2>3, FS_AddElement DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  BY <1>2, PositionsPlusOne, Zenon DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(*  Main invariant proof (unchanged).                                     *)
(***************************************************************************)

LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    BY DEF Inv, vars, OccurrencesBefore, PositionsBefore
  <2>. i <= Len(seq) /\ i' = i + 1 /\ seq' = seq
    BY DEF Next
  <2>0. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
    BY DEF OccurrencesBefore, PositionsBefore
  <2>. USE OccurrencesType DEF TypeOK
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
    <3>1. i \in PositionsBefore(seq[i], i+1)
      BY DEF PositionsBefore
    <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
      BY <3>1, PositionsFinite, FS_EmptySet DEF OccurrencesBefore
    <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
      BY <2>1, OccurrencesPlusOne DEF Inv
    <3>4. ASSUME NEW v \in Value \ {seq[i]}
          PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
      BY <2>1, OccurrencesPlusOne DEF Inv
    <3>. QED  BY <2>0, <2>1, <3>2, <3>3, <3>4 DEF Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
    BY <2>0, <2>2, OccurrencesPlusOne DEF Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
    <3>10. cnt' <= OccurrencesBefore(cand', i')
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>20. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>30. ASSUME NEW v \in Value \ {cand'}
           PROVE  2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>. QED  BY <2>0, <2>3, <3>10, <3>20, <3>30 DEF Inv
  <2>. QED  BY <2>1, <2>2, <2>3 DEF Next
<1>3. TypeOK /\ Inv => Correct
  BY OccurrencesType DEF TypeOK, Inv, Correct, Occurrences
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================