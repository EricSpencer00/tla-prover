---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES cand, cnt, stage, seq

vars == <<cand, cnt, stage, seq>>

States == {"init", "run", "done"}
Outcomes == Value \cup {"none", "draw"}

\* The populated indices below any index form a finite subset of the integers.
Indices(i) == {j \in 0..(i - 1) : TRUE}

\* Occurrence counting function: how many times v appears in the positions indexed
\* by the given finite set.
Count(v, S) == Cardinality({j \in S : seq[j] = v})

TypeOK ==
  /\ cand \in Value \cup {"none", "draw"}
  /\ cnt \in 0..Cardinality(Value)
  /\ stage \in States
  /\ seq \in [0..(Cardinality(Value) - 1) -> Value]

Init ==
  /\ cand = "none"
  /\ cnt = 0
  /\ stage = "init"
  /\ seq = [i \in 0..(Cardinality(Value) - 1) |-> CHOOSE x \in Value : TRUE]

\* The first scan of the sequence, as in the main specification.
Vote(i, v) ==
  /\ stage = "run"
  /\ i < Cardinality(Value)
  /\ (cnt = 0 \/ seq[i] = cand)
  /\ cand' = IF cnt = 0 THEN seq[i] ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
  /\ stage' = IF i + 1 = Cardinality(Value) THEN "done" ELSE "run"
  /\ UNCHANGED seq

\* Reset the candidate and counter for the confirmation phase.
Reset ==
  /\ stage = "done"
  /\ cand' = "none"
  /\ cnt' = 0
  /\ UNCHANGED <<stage, seq>>

Confirm(v) ==
  /\ stage = "done"
  /\ cand = "none"
  /\ Count(v, Indices(Cardinality(Value))) > Cardinality(Value) \div 2
  /\ cnt >= Count(v, Indices(Cardinality(Value)))  \* no element can outrun a majority
  /\ cand' = v
  /\ cnt' = 0
  /\ UNCHANGED <<stage, seq>>

Draw ==
  /\ stage = "done"
  /\ cand = "none"
  /\ COUNT_NONE == \A v \in Value : ~(Count(v, Indices(Cardinality(Value))) > Cardinality(Value) \div 2)
  /\ COUNT_NONE
  /\ cand' = "draw"
  /\ cnt' = 0
  /\ UNCHANGED <<stage, seq>>

ResetAgain ==
  /\ stage = "done"
  /\ cand \in Value \cup {"draw"}
  /\ stage' = "init"
  /\ UNCHANGED <<cand, cnt, seq>>

Next ==
  \/ \E i \in 0..(Cardinality(Value) - 1), v \in Value : Vote(i, v)
  \/ Reset
  \/ \E v \in Value : Confirm(v)
  \/ Draw
  \/ ResetAgain

Spec == Init /\ [][Next]_vars

\* The inductive invariant from the main specification, lifted unchanged.
Inv ==
  /\ (stage = "init" => cnt = 0 /\ cand = "none")
  /\ (stage = "run" => cnt >= 1 /\ cand \in Value)
  /\ (stage = "done" => cnt = 0 /\ cand \in Value \cup {"draw", "none"})

\* A strict majority is unique, and it must be the candidate.
Correct ==
  \A v \in Value :
    (Count(v, Indices(Cardinality(Value))) > Cardinality(Value) \div 2) => (cand = v)

\* Type-correctness is invariant.
TypeOKInv == TypeOK

=============================================================================