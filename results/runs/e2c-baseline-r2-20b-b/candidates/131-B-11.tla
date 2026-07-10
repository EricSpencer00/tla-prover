---- MODULE MajorityProof
EXTENDS Majority, FiniteSetTheorems, TLAPS

LEMMA TypeCorrect == Spec => []TypeOK

LEMMA PositionsOne == \A v : PositionsBefore(v,1) = {}

LEMMA PositionsType == \A v, j : PositionsBefore(v,j) \in SUBSET (1 .. j-1)

LEMMA PositionsFinite == \A v, j : IsFiniteSet(PositionsBefore(v,j))

LEMMA PositionsPlusOne ==
  \A j \in 1 .. Len(seq) :
  \A v :
    PositionsBefore(v, j+1) =
    IF seq[j] = v THEN PositionsBefore(v,j) \union {j}
    ELSE PositionsBefore(v,j)

LEMMA OccurrencesType == \A v : \A j \in Int : OccurrencesBefore(v,j) \in Nat

LEMMA OccurrencesOne == \A v : OccurrencesBefore(v,1) = 0

LEMMA OccurrencesPlusOne ==
  \A j \in 1 .. Len(seq) :
  \A v :
    OccurrencesBefore(v, j+1) =
    IF seq[j] = v THEN OccurrencesBefore(v,j) + 1
    ELSE OccurrencesBefore(v,j)

LEMMA Correctness == Spec => []Correct

====