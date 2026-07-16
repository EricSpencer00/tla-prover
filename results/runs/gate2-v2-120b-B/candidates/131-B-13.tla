---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Type correctness lemma (kept unchanged).                                *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK           BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'  BY DEF TypeOK, Next, vars
<1>. QED                    BY <1>1, <1>2, PTL DEF Spec

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

LEMMA OccurrencesType ==
  \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat
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
       <2>2. Cardinality(PositionsBefore(v, j+1)) =
            Cardinality(PositionsBefore(v,j)) + 1
            BY <2>1, FS_CardinalityAdd
       <2>. QED BY <2>2, DEF OccurrencesBefore
  <1>2. CASE seq[j] # v
       <2>. QED BY PositionsPlusOne, DEF OccurrencesBefore
  <1>. QED BY <1>1, <1>2

(***************************************************************************)
(* Invariant and its preservation proof                                    *)
(***************************************************************************)

VARIABLES seq, i, cand, cnt

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< i - 1 - cnt

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0
  /\ \A v \in Value : OccurrencesBefore(v, i) = 0

Next ==
  \/ /\ cnt = 0
        /\ cand' = seq[i]
        /\ cnt' = 1
        /\ i' = i + 1
        /\ UNCHANGED seq
        /\ UNCHANGED cand
  \/ /\ cnt # 0 /\ cand = seq[i]
        /\ cand' = cand
        /\ cnt' = cnt + 1
        /\ i' = i + 1
        /\ UNCHANGED seq
  \/ /\ cnt # 0 /\ cand # seq[i]
        /\ cand' = cand
        /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ UNCHANGED seq

vars == <<seq, i, cand, cnt>>

Spec == Init /\ [] [Next]_vars

(* Inductive invariant preservation proof. *)
LEMMA InvPreserved ==
  ASSUME TypeOK, Inv, Next
  PROVE Inv'
PROOF
  CASES
    \* Case 1: cnt = 0, we reset cnt to 1 and set cand to seq[i]
    <1>1. cnt = 0
      <2>1. cand' = seq[i] /\ cnt' = 1 /\ i' = i + 1
      <2>2. OccurrencesBefore(cand', i') = OccurrencesBefore(seq[i], i+1)
            BY DEF OccurrencesBefore
      <2>3. 1 =< OccurrencesBefore(seq[i], i+1)
            BY PositionsFinite, PositionsOne, PositionsPlusOne,
               FS_AddElement, DEF PositionsBefore, OccurrencesBefore
      <2>4. cnt' =< OccurrencesBefore(cand', i')
            BY <2>1, <2>3
      <2>5. 2 * (OccurrencesBefore(cand', i') - cnt') =< i' - 1 - cnt'
            = 2 * (OccurrencesBefore(seq[i], i+1) - 1)
            =< (i+1) - 1 - 1
            BY <2>1, <2>3, NatArithmetic, ARITHMETIC
      <2>6. \A v \in Value \ {cand'} :
              2 * OccurrencesBefore(v, i') =< i' - 1 - cnt'
            PROOF
              FIX v
              CASE v = seq[i]
                <3>1. v \in Value \ {cand'}  \* impossible because cand' = seq[i]
                <3>. QED  BY <3>1
              CASE v # seq[i]
                <3>2. 2 * OccurrencesBefore(v, i) =< i - 1 - cnt
                      BY Inv
                <3>3. OccurrencesBefore(v, i+1) = OccurrencesBefore(v, i)
                      BY OccurrencesPlusOne, <1>1, <3>2
                <3>4. 2 * OccurrencesBefore(v, i+1) =< i - 1 - cnt
                      BY <3>2, <3>3
                <3>5. i' - 1 - cnt' = (i+1) - 1 - 1 = i - 1 - cnt
                      BY <2>1
                <3>. QED  BY <3>4, <3>5
            QED
      <2>. QED  BY <2>4, <2>5, <2>6, DEF Inv

    \* Case 2: cnt # 0 and cand = seq[i]
    <1>2. cnt # 0 /\ cand = seq[i]
      <2>1. cnt' = cnt + 1 /\ i' = i + 1 /\ cand' = cand
      <2>2. cnt' =< OccurrencesBefore(cand', i')
            =   cnt + 1 =< OccurrencesBefore(cand, i) + 1
            =   OccurrencesBefore(cand, i+1)
            BY OccurrencesPlusOne, <1>2, NatLeqTransitivity
      <2>3. 2 * (OccurrencesBefore(cand', i') - cnt') =
            2 * (OccurrencesBefore(cand, i+1) - (cnt+1))
            =   2 * ((OccurrencesBefore(cand, i) + 1) - cnt - 1)
            =   2 * (OccurrencesBefore(cand, i) - cnt)
            =< i - 1 - cnt
            BY Inv, NatArithmetic
            =   (i+1) - 1 - (cnt+1)
            =   i' - 1 - cnt'
      <2>4. \A v \in Value \ {cand'} :
              2 * OccurrencesBefore(v, i') =< i' - 1 - cnt'
            PROOF
              FIX v
              CASE v = cand   \* not possible because v ∈ Value \ {cand'}
                <3>1. FALSE
                <3>. QED  BY <3>1
              CASE v # cand
                <3>2. 2 * OccurrencesBefore(v, i) =< i - 1 - cnt
                      BY Inv
                <3>3. OccurrencesBefore(v, i+1) = OccurrencesBefore(v, i)
                      BY OccurrencesPlusOne, <1>2, <3>2
                <3>4. 2 * OccurrencesBefore(v, i+1) =< i - 1 - cnt
                      BY <3>2, <3>3
                <3>5. i' - 1 - cnt' = (i+1) - 1 - (cnt+1) = i - 1 - cnt
                      BY <2>1
                <3>. QED  BY <3>4, <3>5
            QED
      <2>. QED  BY <2>2, <2>3, <2>4, DEF Inv

    \* Case 3: cnt # 0 and cand # seq[i]
    <1>3. cnt # 0 /\ cand # seq[i]
      <2>1. cnt' = cnt - 1 /\ i' = i + 1 /\ cand' = cand
      <2>2. cnt' =< OccurrencesBefore(cand', i')
            =   cnt - 1 =< OccurrencesBefore(cand, i) - 1
            =   OccurrencesBefore(cand, i+1) - 1
            =   OccurrencesBefore(cand', i') - 1
            BY OccurrencesPlusOne, <1>3, NatLeqTransitivity
      <2>3. 2 * (OccurrencesBefore(cand', i') - cnt') =
            2 * (OccurrencesBefore(cand, i+1) - (cnt-1))
            =   2 * (OccurrencesBefore(cand, i) + 1 - cnt + 1)
            =   2 * (OccurrencesBefore(cand, i) - cnt) + 4
            =< i - 1 - cnt + 4
            =   (i+1) - 1 - (cnt-1)
            =   i' - 1 - cnt'
            BY Inv, NatArithmetic, ARITHMETIC
      <2>4. \A v \in Value \ {cand'} :
              2 * OccurrencesBefore(v, i') =< i' - 1 - cnt'
            PROOF
              FIX v
              CASE v = cand
                <3>1. v ∉ Value \ {cand'}  \* impossible
                <3>. QED  BY <3>1
              CASE v # cand
                <3>2. 2 * OccurrencesBefore(v, i) =< i - 1 - cnt
                      BY Inv
                <3>3. OccurrencesBefore(v, i+1) = OccurrencesBefore(v, i)
                      BY OccurrencesPlusOne, <1>3, <3>2
                <3>4. 2 * OccurrencesBefore(v, i+1) =< i - 1 - cnt
                      BY <3>2, <3>3
                <3>5. i' - 1 - cnt' = (i+1) - 1 - (cnt-1) = i - 1 - cnt + 2
                      BY <2>1
                <3>6. Since 2 * OccurrencesBefore(v, i+1) ≤ i - 1 - cnt,
                      it also ≤ i - 1 - cnt + 2 = i' - 1 - cnt'
                <3>. QED  BY <3>4, <3>5, NatLeqTransitivity
            QED
      <2>. QED  BY <2>2, <2>3, <2>4, DEF Inv
  QED

=============================================================================