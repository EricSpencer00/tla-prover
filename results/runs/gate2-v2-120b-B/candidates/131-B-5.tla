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
BY DEF OccurrencesBefore, PositionsOne

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY PositionsPlusOne, <1>1
  <2>2. Cardinality(PositionsBefore(v, j+1)) =
        Cardinality(PositionsBefore(v,j)) + 1
    BY <2>1, FS_AddElement, PositionsFinite
  <2>3. OccurrencesBefore(v, j+1) = OccurrencesBefore(v,j) + 1
    BY DEF OccurrencesBefore, <2>2
  <2>. QED  BY <2>3
<1>2. CASE seq[j] # v
  <2>. OccurrencesBefore(v, j+1) = OccurrencesBefore(v,j)
    BY DEF OccurrencesBefore, PositionsPlusOne, <1>2
  <2>. QED  BY <2>
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Invariant (inductive) describing the relationship between counts.       *)
(***************************************************************************)
Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

(***************************************************************************)
(* Correctness based on the invariant.                                     *)
(***************************************************************************)
LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY DEF Init, Inv, OccurrencesOne
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>0. ASSUME TypeOK, Inv, Next
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
    <3>1. i \in PositionsBefore(seq[i], i+1)
      BY DEF PositionsBefore
    <3>2. 1 =< Cardinality(PositionsBefore(seq[i], i+1))
      BY <3>1, FS_EmptySet, FS_AddElement, PositionsFinite
    <3>3. 1 =< OccurrencesBefore(seq[i], i+1)
      BY DEF OccurrencesBefore, <3>2
    <3>4. 2 * (OccurrencesBefore(seq[i], i+1) - 1) =< (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne, <3>3
    <3>5. \A v \in Value \ {seq[i]} :
          2 * OccurrencesBefore(v, i+1) =< (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne, <2>0
    <3>. QED  BY <3>3, <3>4, <3>5, DEF Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
    <3>1. cnt' =< OccurrencesBefore(cand, i+1)
      BY <2>0, OccurrencesPlusOne, <2>2, NatLeqAdd
    <3>2. 2 * (OccurrencesBefore(cand, i+1) - cnt') =< (i+1) - 1 - cnt'
      BY <2>0, OccurrencesPlusOne, <2>2, NatMinusMonotone, NatLeqAdd
    <3>3. \A v \in Value \ {cand} :
          2 * OccurrencesBefore(v, i+1) =< (i+1) - 1 - cnt'
      BY <2>0, OccurrencesPlusOne, <2>2, NatLeqAdd
    <3>. QED  BY <3>1, <3>2, <3>3, DEF Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
    <3>1. cnt' =< OccurrencesBefore(cand, i+1)
      BY <2>0, OccurrencesPlusOne, <2>3, NatLeqMinus1
    <3>2. 2 * (OccurrencesBefore(cand, i+1) - cnt') =< (i+1) - 1 - cnt'
      BY <2>0, OccurrencesPlusOne, <2>3, NatMinusMonotone, NatMinusMinus
    <3>3. \A v \in Value \ {cand} :
          2 * OccurrencesBefore(v, i+1) =< (i+1) - 1 - cnt'
      BY <2>0, OccurrencesPlusOne, <2>3, NatMinusMonotone
    <3>. QED  BY <3>1, <3>2, <3>3, DEF Inv
  <2>. QED  BY <2>1, <2>2, <2>3, DEF Next
<1>3. TypeOK /\ Inv => Correct
  BY DEF Correct, Inv, OccurrencesType
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================