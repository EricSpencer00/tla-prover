---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Helper definitions (unchanged)
\* ----------------------------------------------------------------------
PositionsBefore(v, j) ==
  { k \in 1 .. j-1 : seq[k] = v }

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

\* ----------------------------------------------------------------------
\* Invariant (unchanged)
\* ----------------------------------------------------------------------
Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

\* ----------------------------------------------------------------------
\* Initial predicate (unchanged)
\* ----------------------------------------------------------------------
Init ==
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0
  /\ Inv

\* ----------------------------------------------------------------------
\* Next action (unchanged)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ i <= Len(seq)
     /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED << seq >>
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand = seq[i]
     /\ cnt' = cnt + 1
     /\ i' = i + 1
     /\ UNCHANGED << seq, cand >>
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand # seq[i]
     /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED << seq, cand >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Correctness property
\* ----------------------------------------------------------------------
Correct ==
  /\ i = Len(seq) + 1
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

\* ----------------------------------------------------------------------
\* Type correctness lemma (unchanged)
\* ----------------------------------------------------------------------
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_<<seq, i, cand, cnt>> => TypeOK'
  BY DEF TypeOK, Next, <<seq, i, cand, cnt>>
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

\* ----------------------------------------------------------------------
\* Positions lemmas (unchanged)
\* ----------------------------------------------------------------------
LEMMA PositionsOne == \A v : PositionsBefore(v, 1) = {}
BY DEF PositionsBefore

LEMMA PositionsType == \A v, j : PositionsBefore(v, j) \in SUBSET (1 .. j-1)
BY DEF PositionsBefore

LEMMA PositionsFinite ==
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v, j))
BY 1 \in Int, j-1 \in Int, PositionsType, FS_Interval, FS_Subset, Zenon

LEMMA PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
         ELSE PositionsBefore(v, j)
BY DEF TypeOK, PositionsBefore

\* ----------------------------------------------------------------------
\* Occurrences lemmas (unchanged)
\* ----------------------------------------------------------------------
LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v, j) \in Nat
BY DEF OccurrencesBefore, PositionsFinite, FS_CardinalityType

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
BY PositionsOne, FS_EmptySet, DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
         ELSE OccurrencesBefore(v, j)
BY DEF OccurrencesBefore, PositionsPlusOne

\* ----------------------------------------------------------------------
\* Main correctness lemma (unchanged)
\* ----------------------------------------------------------------------
LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne, DEF Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_<<seq, i, cand, cnt>> => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
    BY DEF Inv, <<seq, i, cand, cnt>>, OccurrencesBefore, PositionsBefore
  <2>. i <= Len(seq) /\ i' = i+1 /\ seq' = seq /\ cand' = cand /\ cnt' = cnt \/ 
        (cnt = 0 /\ cand' = seq[i] /\ cnt' = 1) \/ 
        (cnt # 0 /\ cand = seq[i] /\ cnt' = cnt + 1) \/ 
        (cnt # 0 /\ cand # seq[i] /\ cnt' = cnt - 1)
    BY DEF Next
  <2>0. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
    BY DEF OccurrencesBefore, PositionsBefore
  <2>. USE OccurrencesType DEF TypeOK
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
    <3>1. i \in PositionsBefore(seq[i], i+1)
      BY DEF PositionsBefore
    <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
      BY <3>1, PositionsFinite, FS_EmptySet DEF OccurrencesBefore
    <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>4. ASSUME NEW v \in Value \ {seq[i]}
          PROVE  2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
      BY <2>0, OccurrencesPlusOne DEF Inv
    <3>. QED  BY <3>2, <3>3, <3>4 DEF Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
    BY <2>0, <2>2, OccurrencesPlusOne DEF Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
    <3>10. cnt' <= OccurrencesBefore(cand', i')
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>20. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>30. ASSUME NEW v \in Value \ {cand'}
           PROVE  2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
      BY <2>3, OccurrencesPlusOne DEF Inv
    <3>. QED  BY <3>10, <3>20, <3>30 DEF Inv
  <2>. QED  BY <2>1, <2>2, <2>3 DEF Next
<1>3. TypeOK /\ Inv => Correct
  BY OccurrencesType, DEF TypeOK, Inv, Correct
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

=============================================================================