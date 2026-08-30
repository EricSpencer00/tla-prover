---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES seq, pos, candidate, seen, occCount

vars == <<seq, pos, candidate, seen, occCount>>

Init ==
    /\ seq \in Seq(Value)
    /\ pos \in 0..Len(seq)
    /\ candidate \in Value
    /\ seen \subseteq 0..(Len(seq) - 1)
    /\ occCount \in [Value -> 0..Len(seq)]

Next ==
    \/ \E i \in 0..(Len(seq) - 1) :
         /\ i \notin seen
         /\ occCount' = [occCount EXCEPT ![seq[i]] = @ + 1]
         /\ seen' = seen \cup {i}
    \/ \E v \in Value : candidate' = v
    /\ UNCHANGED <<seq, pos>>

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in Seq(Value)
    /\ pos \in 0..Len(seq)
    /\ candidate \in Value
    /\ seen \subseteq 0..(Len(seq) - 1)
    /\ occCount \in [Value -> 0..Len(seq)]

Majority(v) == occCount[v] * 2 > Len(seq)

Inv ==
    /\ seen \subseteq 0..(Len(seq) - 1)
    /\ \A a, b \in seen : a <= b => \A k \in a..b : seq[k] \in seen
    /\ \A v \in Value : occCount[v] = Cardinality({ i \in seen : seq[i] = v })

Correct ==
    \A v \in Value : Majority(v) => v = candidate

====