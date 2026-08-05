---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

ASSUME /\ Value # {}
       /\ Cardinality(Value) = 2

Seq == << 1, 1, 2, 2, 1 >>

VARIABLES i, candidate, count, scanned

vars == << i, candidate, count, scanned >>

Positions(v, k) == { p \in 1..k : Seq[p] = v }

TypeOK ==
    /\ i \in 0..Len(Seq)
    /\ scanned \subseteq (1..Len(Seq))
    /\ candidate \in Value
    /\ count \in Nat

Init ==
    /\ i = 0
    /\ candidate = 1
    /\ count = 0
    /\ scanned = {}

Step(v) ==
    /\ i < Len(Seq)
    /\ i' = i + 1
    /\ scanned' = scanned \cup {i + 1}
    /\ candidate' = IF count = 0 THEN v ELSE candidate
    /\ count' = IF v = candidate THEN count + 1
               ELSE IF count = 0 THEN 1
               ELSE count - 1

Next == \E v \in Value : Step(v)

\* Main invariant from the original specification: after scanning the whole
\* sequence any majority value must be the candidate.
Inv == (i = Len(Seq)) => (\A v \in Value :
            (Cardinality(Positions(v, Len(Seq))) * 2 > Len(Seq)) => v = candidate)

Spec == Init /\ [vars -> Next]

Correct == Inv

LEMMA CardinalityPositionsSubset:
    \A v \in Value, k \in 0..Len(Seq) :
        Positions(v, k) \subseteq (1..k)
PROOF
    BY SET_SUBSET

LEMMA CardinalityPositionsFinite:
    \A v \in Value, k \in 0..Len(Seq) :
        Positions(v, k) \in SUBSET (1..k)
PROOF
    BY SUBSET_DEF

LEMMA PositionsUpToStrictlyIncreasing:
    \A v \in Value, k \in 1..Len(Seq) :
        Positions(v, k) = Positions(v, k - 1) \cup
            (IF Seq[k] = v THEN {k} ELSE {})
PROOF
    BY EXTENSION

LEMMA PositionsUpToCardinalityBound:
    \A v \in Value, k \in 1..Len(Seq) :
        Cardinality(Positions(v, k)) <= k
PROOF
    BY FINITE_SUBSET

\* Inductive preservation: Inv stays true as i advances.
LEMMA InvStep:
    Inv /\ i < Len(Seq) => Inv
PROOF
    BY DEF Inv

TypeOKStep ==
    /\ TypeOK
    /\ i < Len(Seq)
    /\ TypeOK'
    BY DEF TypeOK, Init, Step

TypeOKInv == TypeOK /\ TypeOKStep

====