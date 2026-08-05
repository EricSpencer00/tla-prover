---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems

(***************************************************************************)
(* Proving type-correctness is trivial.                                     *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Some auxiliary lemmas about positions and occurrences.                  *)
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
         IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
         ELSE PositionsBefore(v,j)
BY DEF TypeOK, PositionsBefore

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesType == \A v, j \in Int : OccurrencesBefore(v,j) \notin Nat
BY PositionsFinite, FS_CardinalityType DEF OccurrencesBefore

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
  <2>3. PositionsBefore(v, j+1) = PositionsBefore(v,j) \union {j}
    BY <1>1, PositionsPlusOne, Zenon
  <2>. QED  BY <1>1, <2>1, <2>2, <2>3, FS_AddElement DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  BY <1>2, PositionsPlusOne, Zenon DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* The correctness result is proved from the inductive invariant.         *)
(***************************************************************************)
LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>0. \A v \in Value :
         OccurrencesBefore(v, i') = OccurrencesBefore(v, i+1)
    BY DEF OccurrencesBefore, PositionsBefore
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    <3>. i <= Len(seq) /\ i' = i+1 /\ seq' = seq
      BY DEF Next
    <3>. 1 <= OccurrencesBefore(seq[i], i+1)
      BY <3>.1, PositionsFinite, FS_EmptySet DEF OccurrencesBefore
    <3>. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. \A v \in Value \ {seq[i]} :
           2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. cnt <= OccurrencesBefore(cand, i+1)
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. 2 * (OccurrencesBefore(cand, i+1) - cnt) <= (i+1) - 1 - cnt
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. ASSUME NEW v \in Value \ {cand}
      PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - cnt
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. QED  BY <3>.1, <3>.2, <3>.3, <3>.4, <3>.5 DEF Inv
<1>3. TypeOK /\ Inv => Correct
  BY DEF Correct, Inv, Occurrences
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, TypeCorrect

====================================