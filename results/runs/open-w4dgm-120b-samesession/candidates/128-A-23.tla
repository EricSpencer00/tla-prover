---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

Lobes == {i \in 1..MaxSeqLen : i <= Len(seq)}
Blank == "blank"
Loop == "loop"
Term == "term"

VARIABLES seq, saved, todo, pc

vars == <<seq, saved, todo, pc>>

TypeOK ==
    /\ seq \in Seq(Values)
    /\ saved \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ Len(saved) <= MaxSeqLen
    /\ todo \subseteq [l: 1..MaxSeqLen, u: 1..MaxSeqLen]
    /\ pc \in {Loop, Term}

Init ==
    /\ \E s \in Seq(Values) : Len(s) >= 1 /\ seq = s
    /\ saved = seq
    /\ todo = {[l |-> 1, u |-> Len(seq)]}
    /\ pc = Loop

\* The partition operator is nondeterministic over the set of all valid
\* results a real partition step could produce, so the action itself stays
\* deterministic apart from that choice.
Permutes(p) == {q \in [1..Len(seq) -> Values] :
                    /\ \A i \in 1..Len(seq) : q[i] \in Values
                    /\ \A i \in 1..Len(seq) : \E j \in 1..Len(seq) : q[i] = seq[j]
                    /\ \A i \in 1..Len(seq) : i > Len(p) => q[i] = seq[i]
                    /\ \A i \in Lobes : i <= Len(p) => q[i] <= p[i]}
Split(oo, l, u) == IF l = u THEN 0 ELSE IF oo[l] < oo[l+1]
                    THEN 2 * oo[l + 1] - oo[l]
                    ELSE oo[l]

AfterStep ==
    \E r \in todo :
        \/ (\A i \in 1..Len(seq) : r.l <= i /\ i <= r.u => seq[i] = saved[i])
        /\ \A i \in 1..Len(seq) : seq[i] = saved[i]
        /\ \A i \in Lobes : \A j \in Lobes :
                (r.l <= i /\ i <= r.u /\ r.l <= j /\ j <= r.u /\ i > j)
                    => seq[i] >= seq[j]

Step ==
    /\ pc = Loop
    /\ \/ \E r \in todo :
            /\ r.l = r.u
            /\ todo' = todo \ {r}
            /\ UNCHANGED <<seq saved>>
       \/ \E r \in todo, k \in r.l .. r.u :
            /\ \E q \in Permutes(k) : seq' = q
            /\ saved' = seq
            /\ todo' = (todo \ {r}) \cup
                        {[l |-> r.l, u |-> k], [l |-> k + 1, u |-> r.u]}
            /\ pc' = IF \E t \in todo : t.l = t.u THEN Term ELSE Loop
    /\ AfterStep

Idle ==
    /\ pc = Term
    /\ UNCHANGED vars

Next == Step \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The invariant combines the three facets that together imply the sorted
\* permutation on termination.
Inv ==
    /\ \A i \in Lobes, j \in Lobes : i > j => seq[i] >= seq[j]
    /\ \A i \in 1..Len(seq) : \E j \in 1..Len(seq) : seq[i] = saved[j]
    /\ \A i \in 1..Len(seq), j \in 1..Len(seq) : i > j => seq[i] >= seq[j]

PCorrect == (pc = Term) => Inv
TypeOKP    == TypeOK
Termination == (pc = Loop) ~> (pc = Term)
====