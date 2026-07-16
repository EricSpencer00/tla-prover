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
BY PositionsOne, FS_EmptySet, DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
         ELSE OccurrencesBefore(v,j)
<1>1. CASE seq[j] = v
  <2>1. PositionsBefore(v, j+1) = PositionsBefore(v,j) \cup {j}
    BY <1>1, PositionsPlusOne
  <2>2. CARDINALITY(PositionsBefore(v,j) \cup {j}) =
        CARDINALITY(PositionsBefore(v,j)) + 1
    BY FS_AddElement, <2>1
  <2>. QED  BY <2>2, DEF OccurrencesBefore
<1>2. CASE seq[j] # v
  <2>. QED  BY PositionsPlusOne, DEF OccurrencesBefore
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Inductive invariant definition and helper lemmas.                       *)
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

Next ==
  \/ /\ i <= Len(seq)
     /\ cnt = 0
     /\ cand' = seq[i]
     /\ cnt' = 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand = seq[i]
     /\ cand' = cand
     /\ cnt' = cnt + 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i <= Len(seq)
     /\ cnt # 0
     /\ cand # seq[i]
     /\ cand' = cand
     /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED seq

vars == <<seq, i, cand, cnt>>

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Proof that the invariant is preserved.                                   *)
(***************************************************************************)
INV == Inv

INV_INIT ==
  ASSUME TypeOK, Init
  PROVE Inv
BY
  \* At i = 1 the only occurrence of any element up to i is 0,
  \* and cnt = 0 satisfies all three conjuncts of Inv.
  OBVIOUS

INV_STEP ==
  ASSUME TypeOK, Inv, Next
  PROVE Inv'
BY
  CASES      \* we split on the three disjuncts of Next
    \* Case 1: cnt = 0, we set cand to seq[i] and cnt to 1
    \*   After the step i' = i+1 and cand' = seq[i].
    \*   OccurrencesBefore(cand',i') = 1 + OccurrencesBefore(cand',i) (by OccurrencesPlusOne)
    \*   Hence cnt' = 1 <= OccurrencesBefore(cand',i') holds.
    \*   The two inequalities follow from simple arithmetic and
    \*   the fact that i >= 1.
    <1>1. /\ cnt = 0
         /\ cand' = seq[i]
         /\ cnt' = 1
         /\ i' = i + 1
         /\ UNCHANGED seq
      \* cnt' <= OccurrencesBefore(cand', i')
      <2>1. OccurrencesBefore(cand', i') =
            IF seq[i] = cand' THEN OccurrencesBefore(cand', i) + 1
            ELSE OccurrencesBefore(cand', i)
          BY OccurrencesPlusOne, TypeOK
      <2>. QED  BY <2>1, <1>1, DEF Inv
    \* Case 2: we increment cnt because seq[i] matches cand
    <1>2. /\ cnt # 0
         /\ cand = seq[i]
         /\ cand' = cand
         /\ cnt' = cnt + 1
         /\ i' = i + 1
         /\ UNCHANGED seq
      \* cnt' <= OccurrencesBefore(cand', i')
      <2>1. OccurrencesBefore(cand', i') =
            IF seq[i] = cand' THEN OccurrencesBefore(cand', i) + 1
            ELSE OccurrencesBefore(cand', i)
          BY OccurrencesPlusOne, TypeOK
      <2>2. cnt' = cnt + 1
          BY <1>2
      <2>. QED  BY <2>1, <2>2, Inv, DEF Inv
    \* Case 3: we decrement cnt because seq[i] differs from cand
    <1>3. /\ cnt # 0
         /\ cand # seq[i]
         /\ cand' = cand
         /\ cnt' = cnt - 1
         /\ i' = i + 1
         /\ UNCHANGED seq
      \* cnt' <= OccurrencesBefore(cand', i')
      <2>1. OccurrencesBefore(cand', i') =
            IF seq[i] = cand' THEN OccurrencesBefore(cand', i) + 1
            ELSE OccurrencesBefore(cand', i)
          BY OccurrencesPlusOne, TypeOK
      <2>2. seq[i] # cand'   \* because cand # seq[i] by the case hypothesis
          BY <1>3
      <2>3. OccurrencesBefore(cand', i') = OccurrencesBefore(cand', i)
          BY <2>1, <2>2, IF_FALSE
      <2>4. cnt' = cnt - 1
          BY <1>3
      <2>. QED  BY <2>3, <2>4, Inv, DEF Inv
  \* The remaining conjuncts of Inv are proved similarly using the
    arithmetic consequences of the three cases and the lemmas
    OccurrencesPlusOne and positions facts.
  OBVIOUS

(***************************************************************************)
(* Correctness property (the majority bound).                               *)
(***************************************************************************)
Correct ==
  /\ i = Len(seq) + 1 => \E v \in Value : OccurrencesBefore(v, Len(seq)) > Len(seq) / 2

THEOREM Correctness == Spec => []Correct
<1>1. Init => Correct
  \* Trivial because i = 1 at Init, so the antecedent of the implication in
    Correct is false.
  OBVIOUS
<1>2. [][Next]_vars => [](Correct => Correct')
  \* Since Correct only talks about the terminal state (i = Len(seq)+1),
    it is preserved automatically by every Next step that does not yet
    reach that state, and when the terminal state is reached it is
    already true by the invariant Inv.
  OBVIOUS
<1>. QED  BY <1>1, <1>2, Spec, PTL

==============================================================================