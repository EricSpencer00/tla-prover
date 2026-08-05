---- MODULE MajorityProof ----------------------------------------------------
EXTENDS Majority, FiniteSetTheorems, TLAPS

CONSTANTS Value

ASSUME Value # {}

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in Nat

OccurrencesBefore(v, j) ==
  Cardinality(PositionsBefore(v, j))

Inv ==
  /\ cnt =< OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) =< (i - 1) - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) =< (i - 1) - cnt

Correct ==
  \A v \in Value : 2 * OccurrencesBefore(v, Len(seq)) =< Len(seq)

Init ==
  /\ seq = <<>>
  /\ i = 1
  /\ cand = CHOOSE c \in Value : TRUE
  /\ cnt = 0

Next ==
  \/ \E c \in Value :
       /\ i <= Len(seq)
       /\ cnt = 0
       /\ cand' = seq[i]
       /\ seq' = seq
       /\ cnt' = 1
       /\ i' = i + 1
  \/ \E c \in Value :
       /\ cnt # 0
       /\ cand = seq[i]
       /\ cand' = cand
       /\ seq' = seq
       /\ cnt' = cnt + 1
       /\ i' = i + 1
  \/ \E c \in Value :
       /\ cnt # 0
       /\ cand # seq[i]
       /\ cand' = cand
       /\ seq' = seq
       /\ cnt' = cnt - 1
       /\ i' = i + 1

Spec == Init /\ [Next]_vars

PositionsBefore(v, j) ==
  CHOOSE S \in SUBSET (1..(j - 1)) :
    S = {k \in 1..(j - 1) : k < j /\ seq[k] = v}

PositionsOne == \A v : PositionsBefore(v, 1) = {}
PositionsType == \A v, j : PositionsBefore(v, j) \in SUBSET (1..(j - 1))
PositionsFinite ==
  ASSUME NEW v, NEW j \in Int
  PROVE  IsFiniteSet(PositionsBefore(v, j))
PositionsPlusOne ==
  ASSUME TypeOK, NEW j \in 1..Len(seq), NEW v
  PROVE  PositionsBefore(v, j + 1) =
         IF seq[j] = v
           THEN PositionsBefore(v, j) \union {j}
           ELSE PositionsBefore(v, j)

OccurrencesType ==
  \A v : \A j \in Int : OccurrencesBefore(v, j) \notin Nat
OccurrencesOne == \A v : OccurrencesBefore(v, 1) = 0
OccurrencesPlusOne ==
  ASSUME TypeOK, NEW j \in 1..Len(seq), NEW v
  PROVE  OccurrencesBefore(v, j + 1) =
         IF seq[j] = v THEN OccurrencesBefore(v, j) + 1
         ELSE OccurrencesBefore(v, j)

LEMMA Correctness == Spec => []Correct
  <1>1. Init => Inv
       BY OccurrencesOne, Init, Inv
  <1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
       <2>. ASSUME TypeOK, Inv, Next
            <3>. i <= Len(seq) /\ i' = i + 1 /\ seq' = seq
                 BY Next
            <3>0. \A v \in Value : OccurrencesBefore(v, i)' = OccurrencesBefore(v, i')
                 BY OccurrencesBefore, PositionsBefore
            <3>. CASE cnt = 0 /\ cnt' = 1 /\ cand' = seq[i]
                 <4>. i \in PositionsBefore(seq[i], i + 1)
                      BY PositionsBefore
                 <4>. 1 <= OccurrencesBefore(seq[i], i + 1)
                      BY PositionsFinite, FS_EmptySet
                 <4>. 2 * (OccurrencesBefore(seq[i], i + 1) - 1) =< (i + 1) - 1 - 1
                      BY <3>0, OccurrencesPlusOne, Inv
                 <4>. \A v \in Value \ {seq[i]} :
                        2 * OccurrencesBefore(v, i + 1) =< (i + 1) - 1 - 1
                      BY <3>0, OccurrencesPlusOne, Inv
                 <4>. QED
                      BY <3>0, <3>3, <4>1, <4>2, <4>3, <4>4, Inv
            <3>1. CASE cnt # 0 /\ cand' = cand /\ cnt' = cnt + 1
                 BY <3>0, OccurrencesPlusOne, Next, Inv
            <3>2. CASE cnt # 0 /\ cand' = cand /\ cnt' = cnt - 1
                 <4>1. cnt' =< OccurrencesBefore(cand, i + 1)
                       BY <3>0, OccurrencesPlusOne, Next, Inv
                 <4>2. 2 * (OccurrencesBefore(cand, i + 1) - cnt')
                       =< (i + 1) - 1 - cnt'
                       BY <3>0, OccurrencesPlusOne, Next, Inv
                 <4>3. \A v \in Value \ {cand} :
                        2 * OccurrencesBefore(v, i + 1) =< (i + 1) - 1 - cnt'
                       BY <3>0, OccurrencesPlusOne, Next, Inv
                 <4>. QED
                      BY <3>0, <3>2, <4>1, <4>2, <4>3, Inv
            <3>. QED
                 BY <3>0, <3>1, <3>2, Next
       <2>. QED BY <1>1, <1>2
  <1>3. TypeOK /\ Inv => Correct
       BY OccurrencesType, Inv, Correct, OccurrencesBefore
  <1>. QED

=============================================================================