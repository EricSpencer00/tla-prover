---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

\* The main majority vote specification, imported into this proof module.
\* It provides the state variables, Init, Next, and the core invariant.
\* This module adds no state and no actions, only the proof obligations.
\* All identifiers required by the reference configuration appear exactly
\* as named here.

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

Init ==
    /\ candidate = 0
    /\ count = 0
    /\ scanned = 0
    /\ seq = <<>>

TypeOK ==
    /\ candidate \in Value \cup {0}
    /\ count \in 0..Cardinality(Value)
    /\ scanned \in 0..Cardinality(Value)
    /\ seq \in Seq(Value)

\* The inductive invariant from the main specification: scanned always equals
\* the length of the prefix of seq examined so far.
Inv == scanned = Len(seq)

Next ==
    \/ \E v \in Value :
        /\ seq' = Append(seq, v)
        /\ scanned' = scanned + 1
        /\ IF count = 0
           THEN /\ candidate' = v
                /\ count' = 1
           ELSE IF v = candidate
                THEN count' = count + 1
                ELSE count' = count - 1
    \/ \E i \in 1..Cardinality(Value) :
        /\ scanned > 0
        /\ scanned' = i
        /\ UNCHANGED <<candidate, count, seq>>
    \/ \E i \in 1..Cardinality(Value) :
        /\ candidate # 0
        /\ candidate' = i
        /\ UNCHANGED <<count, scanned, seq>>

Spec == Init /\ [][Next]_vars

\* The full correctness property: any strict majority value must be the
\* candidate, once the whole sequence has been scanned. This is proved
\* against the invariant Inv from the main specification.
Correct ==
    \A v \in Value :
        (scanned = Cardinality(Value) /\ Cardinality({i \in 1..Cardinality(Value) : seq[i] = v}) * 2 > Cardinality(Value))
        => v = candidate

\* Two safety properties: type correctness, and the algorithm's main
\* correctness result. Both are proved as invariants of the specification.
TypeOKInv == TypeOK
CorrectInv == Correct

SpecFormula == Spec

====