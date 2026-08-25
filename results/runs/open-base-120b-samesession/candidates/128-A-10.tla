---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Interval == <<i, j>> \* i <= j, both natural numbers

IntRange(int) == { k \in 1..Len(seq) : int[1] <= k /\ k <= int[2] }

LenInterval(int) == int[2] - int[1] + 1

Count(seq, v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

CountOn(seq, lo, hi, v) == Cardinality({ i \in lo..hi : seq[i] = v })

IsSorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

IsPermutation(s1, s2) ==
    \A v \in Values : Count(s1, v) = Count(s2, v)

IsValidPartition(old, new, int, p) ==
    LET lo == int[1] IN hi == int[2] IN
    /\ Len(old) = Len(new)
    /\ \A i \in 1..Len(old) :
          (i < lo \/ i > hi) => new[i] = old[i]
    /\ \A i \in lo..p :
          \A j \in p+1..hi : new[i] <= new[j]
    /\ \A v \in Values :
          CountOn(old, lo, hi, v) = CountOn(new, lo, hi, v)

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ---------- Type invariants ----------
TypeOK ==
    /\ Values \subseteq Int
    /\ MaxSeqLen \in Nat
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ \A i \in 1..Len(seq) : seq[i] \in Values
    /\ \A i \in 1..Len(orig) : orig[i] \in Values
    /\ work \subseteq { <<i, j>> : i \in Nat /\ j \in Nat /\ i <= j /\ i >= 1 /\ j <= Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ---------- Additional invariant ----------
Inv ==
    /\ TypeOK
    /\ \A int \in work :
          /\ int[1] >= 1
          /\ int[2] <= Len(seq)
          /\ int[1] <= int[2]

\* ---------- Initial state ----------
Init ==
    /\ seq \in LimitedSeq(Values)
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ---------- Next-state relation ----------
SelectInterval ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E int \in work :
        LET lo == int[1] IN hi == int[2] IN
        IF lo = hi THEN
            /\ seq' = seq
            /\ orig' = orig
            /\ work' = work \ {int}
            /\ pc' = "Loop"
        ELSE
            /\ \E p \in lo..hi :
                 /\ \E newSeq \in LimitedSeq(Values) :
                       /\ IsValidPartition(seq, newSeq, int, p)
                       /\ seq' = newSeq
                       /\ orig' = orig
                       /\ work' = (work \ {int})
                           \cup (IF lo <= p-1 THEN {<<lo, p-1>>} ELSE {})
                           \cup (IF p+1 <= hi THEN {<<p+1, hi>>} ELSE {})
                       /\ pc' = "Loop"

Terminate ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == SelectInterval \/ Terminate \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Safety property ----------
PCorrect ==
    pc = "Done" => /\ IsSorted(seq)
                  /\ IsPermutation(seq, orig)

\* ---------- Liveness property ----------
Termination == <> (pc = "Done")

\* ---------- Fairness ----------
\* Weak fairness of the main action guarantees eventual termination
\* (the .cfg file may also declare WF_vars(Next))
=============================================================================