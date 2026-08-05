---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)
PositionsOne == \A v : PositionsBefore(v,1) = {}
BY DEF PositionsBefore

PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)
BY DEF PositionsBefore

PositionsFinite == 
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v,j))
BY 1 \in Int, j-1 \in Int, PositionsType, FS_Interval, FS_Subset, Zenon

PositionsPlusOne == /\ TypeOK
  /\ \A j \in 1 .. Len(seq) : \A v :
       PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
         ELSE PositionsBefore(v,j)
BY DEF TypeOK, PositionsBefore

OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \notin Nat
BY PositionsFinite, FS_CardinalityType DEF OccurrencesBefore

OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

OccurrencesPlusOne == /\ TypeOK
  /\ \A j \in 1 .. Len(seq) : \A v :
       OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
BY DEF TypeOK, OccurrencesBefore

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)
Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>1. ASSUME TypeOK, Inv, Next PROVE Inv'
    <3>1. i <= Len(seq) /\ i' = i+1 /\ seq' = seq
      BY DEF Next
    <3>2. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
      BY DEF OccurrencesBefore, PositionsBefore
    <3>3. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
      <4>1. i \in PositionsBefore(seq[i], i+1)
        BY DEF PositionsBefore
      <4>2. 1 <= OccurrencesBefore(seq[i], i+1)
        BY <4>1, PositionsFinite, Zenon, FS_EmptySet DEF OccurrencesBefore
      <4>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
        BY <3>2, <3>3, OccurrencesPlusOne DEF Inv
      <4>4. \A v \in Value \ {seq[i]} :
           2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
        BY <3>2, <3>3, OccurrencesPlusOne DEF Inv
      <4>. QED  BY <3>1, <4>2, <4>3, <4>4 DEF Inv
    <3>4. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
      BY <3>2, <3>3, OccurrencesPlusOne DEF Inv
    <3>5. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
      <4>1. cnt' <= OccurrencesBefore(cand', i+1)
        BY <3>5, <3>2, OccurrencesPlusOne DEF Inv
      <4>2. 2 * (OccurrencesBefore(cand', i+1) - cnt') <= (i+1) - 1 - cnt'
        BY <3>5, <3>2, OccurrencesPlusOne DEF Inv
      <4>3. \A v \in Value \ {cand'} :
           2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - cnt'
        BY <3>5, <3>2, OccurrencesPlusOne DEF Inv
      <4>. QED  BY <3>1, <4>1, <4>2, <4>3 DEF Inv
    <3>. QED  BY <3>3, <3>4, <3>5 DEF Next
  <2>. QED  BY <2>1
<1>3. TypeOK /\ Inv => Correct
  BY OccurrencesType DEF TypeOK, Inv, Correct, Occurrences
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

====