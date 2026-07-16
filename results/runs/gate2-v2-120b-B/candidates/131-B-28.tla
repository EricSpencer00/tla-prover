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
(* Occurrence lemmas.                                                      *)
(***************************************************************************)
LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat
PROOF
  <1>1. \A v : \A j \in Int : Cardinality(PositionsBefore(v,j)) \in Nat
    BY DEF OccurrencesBefore, PositionsFinite, FS_Cardinality
  <1>. QED  BY <1>1
<1> QED

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
BY DEF OccurrencesBefore, PositionsPlusOne, FS_Cardinality

(***************************************************************************)
(* Inductive invariant.                                                    *)
(***************************************************************************)
VARIABLES seq, i, cand, cnt

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

PositionsBefore(v, j) ==
  { k \in 1 .. j-1 : seq[k] = v }

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Init ==
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Value
  /\ seq \in Seq(Value)

Next ==
  \/ /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ cnt # 0 /\ seq[i] = cand
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ cnt # 0 /\ seq[i] # cand
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(***************************************************************************)
(* Correctness theorem.                                                    *)
(***************************************************************************)
Correct ==
  \A v \in Value : 2 * OccurrencesBefore(v, Len(seq)) <= Len(seq)

THEOREM Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne, DEF Init, Inv
<1>2. 
  ASSUME TypeOK, Inv, Next
  PROVE Inv'
  BY
    CASE cnt = 0
      <2>1. cand' = seq[i] /\ cnt' = 1 /\ i' = i + 1
      <2>2. 1 <= OccurrencesBefore(seq[i], i+1)
        BY DEF PositionsBefore, FS_EmptySet, FS_AddElement,
           Cardinality, PositionsFinite
      <2>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
        BY <2>2, PositionsFinite, OccurrencesPlusOne,
           Inv, DEF Inv, TypeOK
      <2>4. \A v \in Value \ {seq[i]} :
            2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>QED  BY <2>1, <2>2, <2>3, <2>4, DEF Inv, Next
    CASE cnt # 0 /\ seq[i] = cand
      <2>1. cand' = cand /\ cnt' = cnt + 1 /\ i' = i + 1
      <2>2. cnt' <= OccurrencesBefore(cand', i')
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>3. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>4. \A v \in Value \ {cand'} :
            2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>QED  BY <2>1, <2>2, <2>3, <2>4, DEF Inv, Next
    CASE cnt # 0 /\ seq[i] # cand
      <2>1. cand' = cand /\ cnt' = cnt - 1 /\ i' = i + 1
      <2>2. cnt' <= OccurrencesBefore(cand', i')
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>3. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>4. \A v \in Value \ {cand'} :
            2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
        BY <2>1, Inv, OccurrencesPlusOne, DEF Inv
      <2>QED  BY <2>1, <2>2, <2>3, <2>4, DEF Inv, Next
  QED
<1>3. TypeOK /\ Inv => Correct
  BY DEF Correct, Inv, OccurrencesBefore, PositionsBefore, FS_Cardinality
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================