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

(***************************************************************************)
(* Cardinality lemmas.                                                     *)
(***************************************************************************)
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

LEMMA OccurrencesType == \A v \in Value : \A j \in Int :
      OccurrencesBefore(v, j) \in Nat
BY DEF OccurrencesBefore, PositionsFinite, FS_Cardinality

LEMMA OccurrencesOne == \A v \in Value : OccurrencesBefore(v,1) = 0
BY PositionsOne, OccurrencesBefore, FS_EmptySet

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v \in Value
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. j \notin PositionsBefore(v,j)
    BY PositionsType
  <2>2. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY <1>1, PositionsPlusOne, Zenon
  <2>3. Cardinality(PositionsBefore(v, j+1)) =
        Cardinality(PositionsBefore(v,j)) + 1
    BY <2>2, FS_CardinalityAddElement, <2>1
  <2>. QED  BY <2>3, OccurrencesBefore, SET_EQUALITY
<1>2. CASE seq[j] # v
  <2>. QED  BY PositionsPlusOne, OccurrencesBefore, Zenon
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Invariant and correctness lemmas.                                       *)
(***************************************************************************)
Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

Correct ==
  \/ i = Len(seq) + 1 /\ cnt = 0
  \/ i = Len(seq) + 1 /\ (\E v \in Value : 2 * OccurrencesBefore(v, Len(seq)) > Len(seq))

LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne, Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    BY DEF Inv, Next, OccurrencesBefore, PositionsBefore, OccurrencesPlusOne, FS_Cardinality
  <2>. QED  BY <2>
<1>3. Inv => Correct
  BY DEF Inv, Correct, OccurrencesBefore, PositionsFinite
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================