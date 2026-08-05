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
         IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
         ELSE PositionsBefore(v,j)
BY DEF TypeOK, PositionsBefore

LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \notin Nat
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
  <2>3. PositionsBefore(v, j+1) = PositionsBefore(v,j) \union {j}
    BY <1>1, PositionsPlusOne, Zenon
  <2>. QED  BY <1>1, <2>1, <2>2, <2>3, FS_AddElement DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  BY <1>2, PositionsPlusOne, Zenon DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)
INVARIANT Inv == \A v \in Value :
  cnt =< OccurrencesBefore(v, i) /\ 2 * (OccurrencesBefore(v, i) - cnt) =< i - 1 - cnt
  /\ \A v' \in Value \ {v} : 2 * OccurrencesBefore(v', i) =< i - 1 - cnt

LEMMA Correctness == Spec => []Inv
<1>1. Init => Inv
  BY OccurrencesOne DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    <3>. \A v \in Value : cnt =< OccurrencesBefore(v, i')
      BY DEF Next, OccurrencesBefore, PositionsBefore, Inv
    <3>. \A v \in Value : 2 * (OccurrencesBefore(v, i') - cnt) =< i' - 1 - cnt
      BY DEF Next, OccurrencesBefore, PositionsBefore, Inv
    <3>. \A v \in Value : \A v' \in Value \ {v} :
           2 * OccurrencesBefore(v', i') =< i' - 1 - cnt
      BY DEF Next, OccurrencesBefore, PositionsBefore, Inv
    <3>. QED  BY <3>1, <3>2, <3>3
<1>3. TypeOK /\ Inv => Correct
  BY DEF Inv, Correct
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================