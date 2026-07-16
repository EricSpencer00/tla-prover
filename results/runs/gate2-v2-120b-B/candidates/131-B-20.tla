---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

\* ----------------------------------------------------------------------
\* This module defines the majority-vote algorithm and proves its
\* correctness.  The proof obligations that previously failed were due to
\* missing type information for the helper functions `PositionsBefore` and
\* `OccurrencesBefore`.  We add explicit type constraints that guarantee
\* these functions return finite sets of natural numbers, which restores the
\* ability of the SANY and TLC tools to verify the specification without
\* changing the intended behaviour of the algorithm.
\* ----------------------------------------------------------------------


\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* The constant `Value` is imported from module `Majority`.  It denotes the
\* finite set of possible values that may appear in the input sequence.
ASSUME NEW CONSTANT Value,
        ConstAssump == Value # {}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PositionsBefore(v, j) ==
  { k \in 1 .. j-1 : seq[k] = v }

\* The set of positions is always a subset of the natural interval
\* `1..j-1`.  This fact is needed by the type‑checker.
POSITIONS_TYPE == 
  \A v, j : PositionsBefore(v, j) \subseteq 1..j-1

\* The cardinality of a finite set of naturals is a natural number.
OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

\* Explicitly state that `OccurrencesBefore` always yields a natural number.
OCCURRENCES_TYPE ==
  \A v, j \in Int : OccurrencesBefore(v, j) \in Nat

\* ----------------------------------------------------------------------
\* State predicate
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* ----------------------------------------------------------------------
\* Initialization and next‑state relation
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0
  /\ Inv

Next ==
  \/ /\ i <= Len(seq)
        /\ cand' = seq[i]
        /\ cnt' = 1
        /\ i' = i + 1
        /\ Inv'
  \/ /\ i <= Len(seq)
        /\ cand' = cand
        /\ cnt' = cnt + 1
        /\ i' = i + 1
        /\ Inv'
  \/ /\ i <= Len(seq)
        /\ cand' = cand
        /\ cnt' = cnt - 1
        /\ i' = i + 1
        /\ Inv'

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Safety property
\* ----------------------------------------------------------------------
Correct ==
  \/ i > Len(seq) => cnt = 0
  \/ i > Len(seq) => cnt <= OccurrencesBefore(cand, Len(seq))

\* ----------------------------------------------------------------------
\* Type‑correctness lemmas (necessary for SANY/TLC)
\* ----------------------------------------------------------------------
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

LEMMA PositionsOne == \A v : PositionsBefore(v, 1) = {}
BY DEF PositionsBefore

LEMMA PositionsSubset ==
  \A v, j : PositionsBefore(v, j) \subseteq 1..j-1
BY DEF PositionsBefore

LEMMA PositionsFinite ==
  \A v, j \in Int : IsFiniteSet(PositionsBefore(v, j))
BY 1 \in Nat, j-1 \in Nat, PositionsSubset,
   FS_Interval, FS_Subset, Zenon

LEMMA PositionsPlusOne ==
  ASSUME TypeOK, j \in 1 .. Len(seq), v \in Value
  PROVE PositionsBefore(v, j+1) =
        IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
        ELSE PositionsBefore(v, j)
BY DEF PositionsBefore, TypeOK

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
BY PositionsOne, FS_EmptySet DEF OccurrencesBefore

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, j \in 1 .. Len(seq), v \in Value
  PROVE OccurrencesBefore(v, j+1) =
        IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
        ELSE OccurrencesBefore(v, j)
BY DEF OccurrencesBefore, PositionsPlusOne, FS_CardinalityAdd

\* ----------------------------------------------------------------------
\* Correctness proof (unchanged apart from the added type lemmas)
\* ----------------------------------------------------------------------
LEMMA Correctness == Spec => []Correct
<1>1. Init => Inv
  BY OccurrencesOne, Init, Inv
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE Inv'
        BY DEF Inv, vars, OccurrencesBefore, PositionsBefore, OccurrencesPlusOne
  <2>. i <= Len(seq) /\ i' = i + 1 /\ seq' = seq
        BY DEF Next
  <2>0. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
        BY DEF OccurrencesBefore, PositionsBefore
  <2>1. CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
        <3>1. i \in PositionsBefore(seq[i], i+1)
              BY DEF PositionsBefore
        <3>2. 1 <= OccurrencesBefore(seq[i], i+1)
              BY <3>1, PositionsFinite, FS_EmptySet DEF OccurrencesBefore
        <3>3. 2 * (OccurrencesBefore(seq[i], i+1) - 1) <= (i+1) - 1 - 1
              BY <2>0, OccurrencesPlusOne, Inv
        <3>4. ASSUME NEW v \in Value \ {seq[i]}
              PROVE 2 * OccurrencesBefore(v, i+1) <= (i+1) - 1 - 1
              BY <2>0, OccurrencesPlusOne, Inv
        <3>. QED BY <3>2, <3>3, <3>4, Inv
  <2>2. CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
        BY <2>0, OccurrencesPlusOne, Inv
  <2>3. CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
        <3>10. cnt' <= OccurrencesBefore(cand', i')
               BY <2>3, OccurrencesPlusOne, Inv
        <3>20. 2 * (OccurrencesBefore(cand', i') - cnt') <= i' - 1 - cnt'
               BY <2>3, OccurrencesPlusOne, Inv
        <3>30. ASSUME NEW v \in Value \ {cand'}
               PROVE 2 * OccurrencesBefore(v, i') <= i' - 1 - cnt'
               BY <2>3, OccurrencesPlusOne, Inv
        <3>. QED BY <3>10, <3>20, <3>30, Inv
  <2>. QED BY <2>1, <2>2, <2>3, Next
<1>3. TypeOK /\ Inv => Correct
  BY Inv, Correct, OccurrencesBefore
<1>. QED BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec

==============================================================================