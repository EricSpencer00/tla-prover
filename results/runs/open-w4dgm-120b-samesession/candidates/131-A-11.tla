---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* Inherits sequence, candidate, seen, and pending from the main spec.
VARIABLES sequence, candidate, seen, pending

vars == <<sequence, candidate, seen, pending>>

TypeOK ==
    /\ sequence \in Seq(Value)
    /\ candidate \in Value \cup {"unset"}
    /\ seen \in SUBSET Value
    /\ pending \in Nat

Init ==
    /\ sequence = <<>>
    /\ candidate = "unset"
    /\ seen = {}
    /\ pending = 0

AppendVote(v) ==
    /\ Len(sequence) < pending
    /\ sequence' = Append(sequence, v)
    /\ UNCHANGED <<candidate, seen, pending>>

SetCandidate(v) ==
    /\ candidate = "unset"
    /\ candidate' = v
    /\ UNCHANGED <<sequence, seen, pending>>

Finish ==
    /\ Len(sequence) = pending
    /\ UNCHANGED vars

Next ==
    \/ \E v \in Value : AppendVote(v)
    \/ \E v \in Value : SetCandidate(v)
    \/ Finish

Spec == Init /\ [][Next]_vars

\* The inductive invariant from the main spec, lifted unchanged.
Inv ==
    /\ (candidate = "unset" => seen = {})
    /\ (candidate # "unset" => seen = {candidate})
    /\ candidate = "unset" => seen = {}
    /\ candidate # "unset" => seen \subseteq {candidate}

TypeOKInv == TypeOK /\ Inv

\* The property about scan completeness: a strict-global-majority value must
\* be exactly the candidate the algorithm settled on.
Correct ==
    /\ candidate # "unset"
    /\ \A v \in Value :
        (Cardinality({i \in 1 .. Len(sequence) : sequence[i] = v}) * 2 > Len(sequence)) => v = candidate

====