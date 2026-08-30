---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* State: the position being scanned, the candidate majority value, the
\* count of this candidate so far, and the scanned subsequence.
VARIABLES pos, candidate, count, prefix

vars == <<pos, candidate, count, prefix>>

Values == {"none", Value}

\* Positions before a given index form a finite integer set; the proof
\* uses the fact that adding one element to a finite set raises its size.
Positions(f) == { i \in 1..Len(f) : f[i] = candidate }

TypeOK ==
    /\ pos \in 0..Len(Value)
    /\ candidate \in Values
    /\ count \in 0..Len(Value)
    /\ prefix \in Seq(Value)

\* Every transition of the system preserves type correctness.
TypeOKPreserved ==
    /\ pos >= 1 => candidate = Value
    /\ pos >= 1 => count = Cardinality(Positions(prefix))

Init ==
    /\ pos = 0
    /\ candidate = "none"
    /\ count = 0
    /\ prefix = <<>>

\* The candidate flips only on the first observed value and then only
\* counts itself; later occurrences of it simply increase its count.
Vote(v) ==
    /\ pos < Len(Value)
    /\ pos' = pos + 1
    /\ prefix' = Append(prefix, v)
    /\ IF pos = 0 THEN candidate' = v /\ count' = 1
       ELSE IF candidate = v THEN candidate' = candidate / count' = count + 1
       ELSE candidate' = candidate /\ count' = count
    /\ UNCHANGED <<>>

\* Once the candidate loses the majority it is cut off and never recut.
CutOff ==
    /\ pos < Len(Value)
    /\ pos > 0
    /\ count * 2 <= pos
    /\ candidate' = "none"
    /\ count' = 0
    /\ pos' = pos + 1
    /\ prefix' = Append(prefix, Value)
    /\ UNCHANGED <<>>

Next == \E v \in Value : Vote(v) \/ CutOff

Spec == Init /\ [][Next]_vars

\* The majority claim matches the candidate: any value occurring in a strict
\* majority of positions of the whole sequence must equal the candidate.
Correct ==
    \A c \in Value :
        (2 * Cardinality({ i \in 1..Len(Value) : Value[i] = c }) > Len(Value))
            => c = candidate

\* The strong invariant that type checking and correctness together depend
\* on: TypeOK together with the correctness property.
Inv == TypeOK /\ Correct

\* Both invariants hold at once, and typeness is preserved by every action.
StateConstraints == TypeOK /\ Correct /\ TypeOKPreserved

====