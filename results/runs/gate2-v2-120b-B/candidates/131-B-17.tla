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
PROOF
  <1>1. \A v, j \in Int : IsFiniteSet(PositionsBefore(v,j))
        BY PositionsFinite
  <1>2. \A v, j \in Int : Cardinality(PositionsBefore(v,j)) \in Nat
        BY <1>1, FS_CardinalityType
  <1>3. \A v, j \in Int : OccurrencesBefore(v,j) = Cardinality(PositionsBefore(v,j))
        BY DEF OccurrencesBefore
  <1>. QED BY <1>2, <1>3
□

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
PROOF
  <1>1. PositionsBefore(v, j+1) = 
        IF seq[j] = v THEN PositionsBefore(v,j) \cup {j}
        ELSE PositionsBefore(v,j)
        BY PositionsPlusOne
  <1>2. \A v,j \in 1..Len(seq) : OccurrencesBefore(v,j) = Cardinality(PositionsBefore(v,j))
        BY DEF OccurrencesBefore
  <1>3. CASE seq[j] = v
        <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
              BY <1>1, <3>1
        <2>2. OccurrencesBefore(v, j+1) = Cardinality(PositionsBefore(v,j)) + 1
              BY <2>1, FS_AddElement, DEF OccurrencesBefore
        <2>. QED BY <2>2, NatPlusOne
     CASE seq[j] # v
        <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j)
              BY <1>1, <3>2
        <2>2. OccurrencesBefore(v, j+1) = Cardinality(PositionsBefore(v,j))
              BY <2>1, DEF OccurrencesBefore
        <2>. QED BY <2>2
  <1>. QED BY <1>3, <1>1, <3>
□

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
  <2>0. \A v \in Value : OccurrencesBefore(v, i') = OccurrencesBefore(v, i) + 
        (IF seq[i] = v THEN 1 ELSE 0)
    BY OccurrencesPlusOne, DEF i'
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
    <3>1. i \in PositionsBefore(seq[i], i+1)
          BY DEF PositionsBefore
    <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
          BY <3>1, PositionsFinite, FS_EmptySet, DEF OccurrencesBefore
    <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
          BY <2>0, OccurrencesPlusOne, <2>1, NatMinusOne, NatTimesTwoLe
    <3>4. ASSUME NEW v \in Value \ {seq[i]}
          PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
          BY <2>0, OccurrencesPlusOne, <2>1, NatMinusOne, NatTimesTwoLe
    <3>. QED  BY <3>2, <3>3, <3>4, DEF Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
    <3>1. cnt' = cnt + 1 <= OccurrencesBefore(cand, i) + 1
          BY <2>0, OccurrencesPlusOne, NatLePlus
    <3>2. 2 * (OccurrencesBefore(cand, i+1) - cnt') <= (i+1) - 1 - cnt'
          BY <2>0, OccurrencesPlusOne, NatMinusLe, NatTimesTwoLe
    <3>3. ASSUME NEW v \in Value \ {cand}
          PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - cnt'
          BY <2>0, OccurrencesPlusOne, NatMinusLe, NatTimesTwoLe
    <3>. QED  BY <3>1, <3>2, <3>3, DEF Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
    <3>1. cnt' <= OccurrencesBefore(cand, i')
          BY <2>0, OccurrencesPlusOne, NatMinusLe
    <3>2. 2 * (OccurrencesBefore(cand, i') - cnt') <= i' - 1 - cnt'
          BY <2>0, OccurrencesPlusOne, NatMinusLe, NatTimesTwoLe
    <3>3. ASSUME NEW v \in Value \ {cand'}
          PROVE  2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
          BY <2>0, OccurrencesPlusOne, NatMinusLe, NatTimesTwoLe
    <3>. QED  BY <3>1, <3>2, <3>3, DEF Inv
  <2>. QED  BY <2>1, <2>2, <2>3, DEF Next
<1>3. TypeOK /\ Inv => Correct
  BY DEF Correct, Inv, OccurrencesBefore, OccurrencesType
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

==============================================================================