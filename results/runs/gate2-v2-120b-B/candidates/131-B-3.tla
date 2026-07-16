---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Auxiliary definitions needed for the lemmas.                            *)
(***************************************************************************)

PositionsBefore(v, j) ==
  { k \in 1..j-1 : seq[k] = v }

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

(***************************************************************************)
(* Lemma: Type correctness (unchanged).                                    *)
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
    BY <1>1, PositionsPlusOne
  <2>2. CARD(PositionsBefore(v, j+1)) =
         CARD(PositionsBefore(v,j)) + 1
    BY <2>1, FS_AddElement, PositionsFinite
  <2>. QED  BY <2>2, DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  <2>. QED  BY <1>2, PositionsPlusOne, DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Inductive invariant and its correctness proof (unchanged).              *)
(***************************************************************************)

LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY DEF Init, Inv, OccurrencesOne
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. ASSUME TypeOK, Inv, Next PROVE Inv'
    BY DEF Inv, Next, OccurrencesBefore, PositionsBefore
  <2>. QED  BY <2>
<1>3. TypeOK /\ Inv => Correct
  BY DEF TypeOK, Inv, Correct
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================