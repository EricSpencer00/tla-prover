---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

PositionsOne == \A v : PositionsBefore(v,1) = {}
BY DEF PositionsBefore

PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)
BY DEF PositionsBefore

OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \notin Nat
BY PositionsFinite, FS_CardinalityType DEF OccurrencesBefore

OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. IsFiniteSet(PositionsBefore(v,j)) BY PositionsFinite
  <2>2. j \notin PositionsBefore(v,j) BY PositionsType
  <2>3. PositionsBefore(v, j+1) = PositionsBefore(v,j) \union {j}
        BY <1>1, PositionsPlusOne, Zenon
  <2>. QED  BY <1>1, <2>1, <2>2, <2>3, FS_AddElement DEF OccurrencesBefore
<1>2. CASE seq[j] # v BY <1>2, PositionsPlusOne, Zenon DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

Correctness == Spec => []Correct
<1>1. Init => Inv BY OccurrencesOne DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    <3>. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
          BY DEF OccurrencesBefore, PositionsBefore
    <3>0. i <= Len(seq) /\ i' = i+1 /\ seq' = seq BY DEF Next
    <3>. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
      <4>1. i \in PositionsBefore(seq[i], i+1) BY DEF PositionsBefore
      <4>2. 1 <= OccurrencesBefore(seq[i], i+1)
            BY <4>1, PositionsFinite, FS_EmptySet DEF OccurrencesBefore
      <4>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
            BY <3>, OccurrencesPlusOne DEF Inv
      <4>4. ASSUME NEW v \in Value \ {seq[i]}
            PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
            BY <3>, OccurrencesPlusOne DEF Inv
      <4>. QED  BY <3>0, <3>0, <4>2, <4>3, <4>4 DEF Inv
    <3>1. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
      BY <3>0, <3>2, OccurrencesPlusOne DEF Inv
    <3>2. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
      <4>10. cnt' <= OccurrencesBefore(cand', i+1)
             BY <3>3, OccurrencesPlusOne DEF Inv
      <4>20. 2 * (OccurrencesBefore(cand', i+1) - cnt')
                <= (i+1) - 1 - cnt' BY <3>3, OccurrencesPlusOne DEF Inv
      <4>30. ASSUME NEW v \in Value \ {cand'}
             PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - cnt'
             BY <3>3, OccurrencesPlusOne DEF Inv
      <4>. QED  BY <3>0, <3>3, <4>10, <4>20, <4>30 DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3 DEF Next
<1>3. TypeOK /\ Inv => Correct BY OccurrencesType DEF TypeOK, Inv, Correct
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

====