---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)
LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}

LEMMA PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)

LEMMA PositionsFinite == \A v, j \in Int : IsFiniteSet(PositionsBefore(v,j))

LEMMA PositionsPlusOne == 
  \A v, j \in Int : j \in 1 .. Len(seq) => 
    PositionsBefore(v, j+1) = 
      IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
      ELSE PositionsBefore(v,j)

LEMMA OccurrencesType == \A v, j \in Int : OccurrencesBefore(v,j) \in Nat

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0

LEMMA OccurrencesPlusOne == 
  \A v, j \in Int : j \in 1 .. Len(seq) => 
    OccurrencesBefore(v, j+1) = 
      IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
      ELSE OccurrencesBefore(v,j)

LEMMA Correctness == Spec => []Correct
====