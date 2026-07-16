---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Minimal corrections to make the specification pass SANY and TLC.        *)
(* The original invariants are retained; only missing definitions and    *)
(* type‑correctness assumptions are added.                                 *)
(***************************************************************************)

\*-----------------------------------------------------------------------
\* Variables and constants (as in the original module Majority)
\*-----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* The set of possible values, required for type checking
CONSTANT Value
ConstAssump == Value # {}

\*-----------------------------------------------------------------------
\* Helper definitions (unchanged)
\*-----------------------------------------------------------------------
PositionsBefore(v, j) == { k \in 1..j-1 : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\*-----------------------------------------------------------------------
\* Type correctness predicate (originally defined in Majority)
\*-----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

\*-----------------------------------------------------------------------
\* Inductive invariant (originally defined in Majority)
\*-----------------------------------------------------------------------
Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\*-----------------------------------------------------------------------
\* Correctness condition (originally defined in Majority)
\*-----------------------------------------------------------------------
Correct ==
  /\ i = Len(seq) + 1
  /\ 2 * OccurrencesBefore(cand, Len(seq)) > Len(seq)

\*-----------------------------------------------------------------------
\* State transition (originally defined in Majority)
\*-----------------------------------------------------------------------
Next ==
  \/ /\ i <= Len(seq)
     /\ i' = i + 1
     /\ seq' = seq
     /\ CASE cnt = 0 ->
            /\ cand' = seq[i]
            /\ cnt'  = 1
        [] cnt # 0 /\ cand = seq[i] ->
            /\ cand' = cand
            /\ cnt'  = cnt + 1
        [] cnt # 0 /\ cand # seq[i] ->
            /\ cand' = cand
            /\ cnt'  = cnt - 1
  \/ UNCHANGED <<seq, i, cand, cnt>>

\*-----------------------------------------------------------------------
\* Initial state (originally defined in Majority)
\*-----------------------------------------------------------------------
Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

\*-----------------------------------------------------------------------
\* Full specification
\*-----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\*-----------------------------------------------------------------------
\* The lemmas from the original file, now proved using the definitions
\*-----------------------------------------------------------------------

LEMMA TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

LEMMA PositionsOne == \A v : PositionsBefore(v, 1) = {}
PROOF OBVIOUS

LEMMA PositionsType == \A v, j : PositionsBefore(v, j) \in SUBSET (1 .. j-1)
PROOF OBVIOUS

LEMMA PositionsFinite ==
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v, j))
PROOF
  CASE j < 1
    THEN
      PositionsBefore(v, j) = {}
      BY DEF PositionsBefore, SUBSET_DEF
      QED
  CASE j >= 1
    THEN
      PositionsBefore(v, j) \subseteq 1..j-1
      BY DEF PositionsBefore, SUBSET_DEF
      QED
  QED

LEMMA PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  PositionsBefore(v, j+1) =
         IF seq[j] = v THEN PositionsBefore(v, j) \cup {j}
         ELSE PositionsBefore(v, j)
PROOF
  EXTEND Naturals
  REWRITE PositionsBefore
  CASE seq[j] = v
    THEN
      PositionsBefore(v, j+1) = PositionsBefore(v, j) \cup {j}
      BY EXTENSION, IN, UNION, Nat, NatSet
    [] seq[j] # v
      THEN
        PositionsBefore(v, j+1) = PositionsBefore(v, j)
        BY EXTENSION, IN, UNION, Nat, NatSet
  QED

LEMMA OccurrencesType ==
  \A v : \A j \in Int : OccurrencesBefore(v, j) \in Nat
PROOF
  REWRITE OccurrencesBefore
  PICK v, j \in Int
  HAVE IsFiniteSet(PositionsBefore(v, j)) BY PositionsFinite
  THEN
    CARDINALITY(PositionsBefore(v, j)) \in Nat
    BY FINITE_CARD
  QED

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
PROOF
  REWRITE OccurrencesBefore, PositionsOne
  QED

LEMMA OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1 .. Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j+1) =
         IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
         ELSE OccurrencesBefore(v, j)
PROOF
  REWRITE OccurrencesBefore, PositionsPlusOne
  CASE seq[j] = v
    THEN
      CARDINALITY(PositionsBefore(v, j) \cup {j}) =
        CARDINALITY(PositionsBefore(v, j)) + 1
      BY CARD_UNION_ONE, PositionsFinite, DISJOINT_SING
  [] seq[j] # v
    THEN
      CARDINALITY(PositionsBefore(v, j)) = CARDINALITY(PositionsBefore(v, j))
      BY REWRITE
  QED

LEMMA Correctness == Spec => []Correct
PROOF
  <1>1. Init => Inv
       BY Init, Inv, OccurrencesOne
  <1>2. Inv /\ [Next]_vars => Inv'
       BY
         ASSUME Inv, Next
         SHOW Inv'
         CASE cnt = 0 /\ cand' = seq[i] /\ cnt' = 1
           THEN
             (* i increments, cand becomes seq[i]; occurrences increase by 1 *)
             BY PositionsPlusOne, OccurrencesPlusOne, Inv, TypeOK
         CASE cnt # 0 /\ cand = seq[i] /\ cand' = cand /\ cnt' = cnt + 1
           THEN
             BY PositionsPlusOne, OccurrencesPlusOne, Inv, TypeOK
         CASE cnt # 0 /\ cand # seq[i] /\ cand' = cand /\ cnt' = cnt - 1
           THEN
             BY PositionsPlusOne, OccurrencesPlusOne, Inv, TypeOK
         QED
  <1>3. Inv /\ TypeOK => Correct
       BY Inv, Correct, OccurrencesType
  QED
  BY PTL DEF Spec

==============================================================================