---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
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

LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat
BY DEF OccurrencesBefore, PositionsFinite, FS_CardinalityType

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. j \notin PositionsBefore(v,j)
    BY PositionsType
  <2>2. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY <1>1, PositionsPlusOne
  <2>3. Cardinality(PositionsBefore(v, j+1)) =
        Cardinality(PositionsBefore(v,j)) + 1
    BY <2>2, FS_AddElement, PositionsFinite
  <2>. QED  BY <1>1, <2>1, <2>3, DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  <2>. QED  BY <1>2, PositionsPlusOne, DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)
LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne, DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    BY DEF Inv, vars, OccurrencesBefore, PositionsBefore
  <2>. i <= Len(seq) /\ i' = i+1 /\ seq' = seq
    BY DEF Next
  <2>0. \A v \in Value : 
          OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
    BY DEF OccurrencesBefore, PositionsBefore
  <2>. USE OccurrencesType, OccurrencesPlusOne
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
    <3>1. i \in PositionsBefore(seq[i], i+1)
      BY DEF PositionsBefore
    <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
      BY <3>1, PositionsFinite, FS_CardinalityType, FS_EmptySet,
         DEF OccurrencesBefore
    <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne, DEF Inv
    <3>4. \A v \in Value \ {seq[i]} :
          2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne, DEF Inv
    <3>. QED  BY <3>2, <3>3, <3>4, DEF Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
    <3>. QED  BY <2>0, OccurrencesPlusOne, DEF Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
    <3>1. cnt' <= OccurrencesBefore(cand', i')
      BY <2>3, OccurrencesPlusOne, DEF Inv
    <3>2. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne, DEF Inv
    <3>3. \A v \in Value \ {cand'} :
          2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne, DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3, DEF Inv
  <2>. QED  BY <2>1, <2>2, <2>3, DEF Next
<1>3. TypeOK /\ Inv => Correct
  BY DEF Correct, Inv, TypeOK
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================