---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Type correctness lemma (kept unchanged).                               *)
(***************************************************************************)
TypeCorrect == Spec => []TypeOK

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)

\* PositionsBefore(v, j) returns the set of indices < j where seq[k] = v.
PositionsBefore(v, j) ==
  { k \in 1..j-1 : seq[k] = v }

PositionsOne == \A v : PositionsBefore(v, 1) = {}

PositionsType == \A v, j : PositionsBefore(v, j) \in SUBSET (1 .. j-1)

PositionsFinite == 
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v, j))
  BY 1 \in Int, j-1 \in Int, PositionsType,
     FS_Interval, FS_Subset, Zenon

PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
         ELSE PositionsBefore(v, j)
  BY DEF PositionsBefore, TypeOK, Zenon

\* OccurrencesBefore(v, j) is the cardinality of PositionsBefore(v, j).
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

OccurrencesType == \A v, j \in Int : OccurrencesBefore(v, j) \in Nat
BY PositionsFinite, FS_CardinalityType DEF OccurrencesBefore

OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
         ELSE OccurrencesBefore(v, j)
  BY DEF OccurrencesBefore, PositionsBefore, PositionsPlusOne, Zenon

(***************************************************************************)
(* Invariant and correctness lemmas (unchanged except for formatting).    *)
(***************************************************************************)

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Correct ==
  \A v \in Value :
    2 * OccurrencesBefore(v, Len(seq)) <= Len(seq) - 1

(***************************************************************************)
(* Proof of correctness (kept unchanged).                                 *)
(***************************************************************************)

LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
    BY OccurrencesOne, Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
    <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
        BY DEF Inv, vars, OccurrencesBefore, PositionsBefore
    <2>. i <= Len(seq) /\ i' = i + 1 /\ seq' = seq
        BY DEF Next
    <2>0. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
        BY DEF OccurrencesBefore, PositionsBefore
    <2>. USE OccurrencesType DEF TypeOK
    <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
        <3>1. i \in PositionsBefore(seq[i], i+1)
            BY DEF PositionsBefore
        <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
            BY <3>1, PositionsFinite, FS_EmptySet,
               DEF OccurrencesBefore
        <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
            BY <2>1, OccurrencesPlusOne, Inv
        <3>4. ASSUME NEW v \in Value \ {seq[i]}
              PROVE 2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
            BY <2>1, OccurrencesPlusOne, Inv
        <3>. QED  BY <2>0, <2>1, <3>2, <3>3, <3>4, DEF Inv
    <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
        BY <2>0, <2>2, OccurrencesPlusOne, DEF Inv
    <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
        <3>10. cnt' <= OccurrencesBefore(cand', i')
            BY <2>3, OccurrencesPlusOne, DEF Inv
        <3>20. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
            BY <2>3, OccurrencesPlusOne, DEF Inv
        <3>30. ASSUME NEW v \in Value \ {cand'}
               PROVE 2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
            BY <2>3, OccurrencesPlusOne, DEF Inv
        <3>. QED  BY <2>0, <2>3, <3>10, <3>20, <3>30, DEF Inv
    <2>. QED  BY <2>1, <2>2, <2>3, DEF Next
<1>3. TypeOK /\ Inv => Correct
    BY Inv, Correct, DEF Correct
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

====