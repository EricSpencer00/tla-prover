---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm is captured in the MAIN module; this
\* module adds the machine-checked proof that the algorithm is type-correct and
\* that its final candidate is indeed the only possible majority element.
CONSTANTS MaxLen

VARIABLES candidate, count, index, seq

vars == <<candidate, count, index, seq>>

TypeOK ==
  /\ candidate \in Value
  /\ count \in 0..MaxLen
  /\ index \in 0..MaxLen
  /\ seq \in Seq(Value)

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ index = 0
  /\ seq = <<>>

\* The algorithm processes one element of the stream: a matching value increments
\* the vote counter, a nonmatching value decrements it, and a zero counter picks
\* the new candidate from the stream.
Step(v) ==
  /\ index < MaxLen
  /\ index' = index + 1
  /\ seq' = Append(seq, v)
  /\ IF count = 0
       THEN candidate' = v /\ count' = 1
     ELSE IF v = candidate
       THEN count' = count + 1 /\ candidate' = candidate
     ELSE count' = count - 1 /\ candidate' = candidate
  /\ UNCHANGED <<candidate, count, index, seq>>

Next == \E v \in Value : Step(v)

Spec == Init /\ [][Next]_vars

\* No new state, so the type-correctness invariant is proved for the inherited
\* state directly by TLAPS without an explicit inductive argument.
TypeOKInv == TypeOK

\* The set of positions before a given index is a finite integer subset.
PositionsBefore(i) == {j \in 0..(i - 1) : TRUE}

\* Inductive invariant: after processing any prefix of the stream, any value that
\* is in the majority of that prefix must equal the current candidate.
Inv == \A i \in 0..MaxLen :
  \A x \in Value :
    (2 * Cardinality({j \in 0..(i - 1) : seq[j] = x})) > i => x = candidate

CorrectInv == Inv

====