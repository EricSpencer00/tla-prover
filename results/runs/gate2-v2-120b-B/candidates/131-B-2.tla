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
BY DEF OccurrencesBefore, PositionsFinite, FS_Cardinality

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY <1>1, PositionsPlusOne
  <2>2. Cardinality(PositionsBefore(v,j) \cup {j}) =
         Cardinality(PositionsBefore(v,j)) + 1
    BY PositionsFinite, FS_AddElement
  <2>. QED  BY <2>1, <2>2, DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  <2>. QED  BY <1>2, PositionsPlusOne, FS_Cardinality, DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Invariant that captures the majority condition.                         *)
(***************************************************************************)
VARIABLES seq, i, cand, cnt

(* Type correctness predicate *)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in Nat

(* Occurrences and Positions definitions *)
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))
PositionsBefore(v, j) == { k \in 1..(j-1) : seq[k] = v }

(* Inductive invariant used in the proof *)
Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(* Next-state relation of the Boyer‑Moore majority algorithm *)
Next ==
  \/ /\ i <= Len(seq)
     /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand = seq[i]
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ i' = i + 1
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand # seq[i]
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ i' = i + 1
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, cand, cnt>>

(* Specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

Init ==
  /\ i = 1
  /\ cnt = 0
  /\ cand \in Value
  /\ seq \in Seq(Value)

(***************************************************************************)
(* Proof that the invariant is inductive.                                   *)
(***************************************************************************)
INV_PROOF ==
  /\ Init => Inv
  /\ Inv /\ [Next]_<<seq,i,cand,cnt>> => Inv'

<1>1. Init => Inv
  BY DEF Init, Inv, OccurrencesOne

<1>2. Inv /\ [Next]_<<seq,i,cand,cnt>> => Inv'
  ASSUME Inv, Next
  CASES
    <2>1. i <= Len(seq) /\ cnt = 0 /\ cand' = seq[i] /\ cnt' = 1 /\ i' = i + 1
      <3>1. cnt' <= OccurrencesBefore(cand', i')
        BY <2>1, OccurrencesPlusOne, OccurrencesOne
      <3>2. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
        BY <2>1, OccurrencesPlusOne, <3>1,
           CALCULATION
             2 * (OccurrencesBefore(seq[i], i+1) - 1)
               = 2 * (OccurrencesBefore(seq[i], i) + 1 - 1)
               = 2 * OccurrencesBefore(seq[i], i)
               <= i - 1 - 0          \* from Inv
               = (i+1) - 1 - 1
        QED
      <3>3. \A v \in Value \ {cand'} :
               2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
        BY <2>1, Inv, OccurrencesPlusOne, <3>1,
           CALCULATION
             For v # seq[i], OccurrencesBefore(v,i+1)=OccurrencesBefore(v,i)
             So the inequality follows from Inv.
        QED
      <3>. QED BY <3>1, <3>2, <3>3

    <2>2. i <= Len(seq) /\ cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1 /\ i' = i + 1
      <3>1. cnt' <= OccurrencesBefore(cand', i')
        BY <2>2, OccurrencesPlusOne, Inv
      <3>2. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
        BY <2>2, Inv, OccurrencesPlusOne,
           CALCULATION
             2 * (OccurrencesBefore(cand, i+1) - (cnt+1))
               = 2 * (OccurrencesBefore(cand, i) + 1 - cnt - 1)
               = 2 * (OccurrencesBefore(cand, i) - cnt)
               <= i - 1 - cnt          \* from Inv
               = (i+1) - 1 - (cnt+1)
        QED
      <3>3. \A v \in Value \ {cand'} :
               2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
        BY <2>2, Inv, OccurrencesPlusOne, <3>1,
           CALCULATION
             For v # cand, the left side does not change,
             while the right side decreases by 1,
             so the inequality is preserved.
        QED
      <3>. QED BY <3>1, <3>2, <3>3

    <2>3. i <= Len(seq) /\ cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1 /\ i' = i + 1
      <3>1. cnt' <= OccurrencesBefore(cand', i')
        BY <2>3, Inv
      <3>2. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
        BY <2>3, Inv, OccurrencesPlusOne,
           CALCULATION
             2 * (OccurrencesBefore(cand, i+1) - (cnt-1))
               = 2 * (OccurrencesBefore(cand, i) - cnt) + 2
               <= i - 1 - cnt + 2
               = (i+1) - 1 - (cnt-1)
        QED
      <3>3. \A v \in Value \ {cand'} :
               2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
        BY <2>3, Inv, OccurrencesPlusOne,
           CALCULATION
             For v # seq[i] and v # cand, the left side stays,
             the right side grows by 1, preserving the inequality.
        QED
      <3>. QED BY <3>1, <3>2, <3>3

    <2>4. i > Len(seq)
      <3>. QED  BY UNCHANGED

  QED

<1>. QED BY <1>1, <1>2

(***************************************************************************)
(* The final properties.                                                    *)
(***************************************************************************)
Correct ==
  /\ i = Len(seq) + 1
  /\ 2 * OccurrencesBefore(cand, Len(seq)) > Len(seq)

THEOREM Spec => []Correct
  BY INV_PROOF, TypeCorrect, Spec, Inv, Correct

=============================================================================