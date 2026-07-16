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
BY DEF OccurrencesBefore, PositionsFinite

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY DEF PositionsOne, OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
        BY <1>1, PositionsPlusOne, Zenon
  <2>2. Cardinality(PositionsBefore(v, j+1)) =
        Cardinality(PositionsBefore(v,j)) + 1
        BY <2>1, FS_AddElement
  <2>. QED  BY <2>2, DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  <2>. QED  BY <1>2, PositionsPlusOne, FS_EmptySet, DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Main invariant, type correctness, and actions.                           *)
(***************************************************************************)
VARIABLES seq, i, cand, cnt

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Correct == \E v \in Value : 
            /\ cnt <= OccurrencesBefore(v, Len(seq))
            /\ 2 * (OccurrencesBefore(v, Len(seq)) - cnt) <= Len(seq) - cnt

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0
  /\ Inv

Next ==
  \/ /\ i <= Len(seq)
     /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED <<seq, cand>>
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ seq[i] = cand
     /\ i' = i + 1
     /\ UNCHANGED <<seq>>
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ seq[i] # cand
     /\ i' = i + 1
     /\ UNCHANGED <<seq>>
  \/ /\ i = Len(seq) + 1
     /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

==============================================================================