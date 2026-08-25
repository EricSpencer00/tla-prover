---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A i \in 1..Len(s1) : \E j \in 1..Len(s2) : s1[i] = s2[j]

Sorted(s) ==
    /\ Len(s) <= 1
    \/ \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* interval is a two‑element sequence <<low, high>>
IntervalLow(I) == I[1]
IntervalHigh(I) == I[2]

\* Partition predicate – abstract version
Partition(old, new, l, u, p) ==
    /\ Len(old) = Len(new)
    /\ \A i \in 1..Len(old) :
          (i < l \/ i > u) => new[i] = old[i]
    /\ \A i \in l..p : \A j \in p+1..u : new[i] <= new[j]

\* ---------- Variables ----------
VARIABLES seq, origSeq, workSet, pc

\* ---------- Types ----------
TypeOK ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ origSeq = seq
    /\ workSet \subseteq { <<l, u>> : l \in 1..Len(seq), u \in l..Len(seq) }
    /\ pc \in {"Run", "Done"}

\* ---------- Invariant ----------
Inv ==
    /\ TypeOK
    /\ IsPermutation(seq, origSeq)

\* ---------- Partial correctness ----------
PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, origSeq))

\* ---------- Initialization ----------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ origSeq = seq
    /\ workSet = { <<1, Len(seq)>> }
    /\ pc = "Run"

\* ---------- Next-state relation ----------
Next ==
    \/ /\ pc = "Run"
       /\ workSet # {}
       /\ \E I \in workSet :
            LET l == IntervalLow(I)
                u == IntervalHigh(I) IN
            \/ /\ l = u
               /\ (* interval of size 1 – just remove it *)
               /\ workSet' = workSet \ {I}
               /\ UNCHANGED <<seq, origSeq, pc>>
            \/ /\ l # u
               /\ \E p \in l..u :
                    /\ \E newSeq \in LimitedSeq(Values) :
                         /\ Partition(seq, newSeq, l, u, p)
                         /\ seq' = newSeq
                         /\ origSeq' = origSeq
                         /\ workSet' = (workSet \ {I}) \cup { <<l, p>>, <<p+1, u>> }
                         /\ pc' = "Run"
    \/ /\ pc = "Run"
       /\ workSet = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, origSeq, workSet>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, origSeq, workSet, pc>>

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

\* ---------- Liveness ----------
Termination == <> (pc = "Done")

\* ---------- Invariants exposed to the model checker ----------
INVARIANT PCorrect
INVARIANT TypeOK
INVARIANT Inv

\* ---------- Properties ----------
PROPERTY Termination

====