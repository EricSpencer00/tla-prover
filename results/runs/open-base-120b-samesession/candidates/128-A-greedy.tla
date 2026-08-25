---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Integers

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded version of Seq
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
Intervals(s) == { <<i, j>> : 1 <= i /\ i <= j /\ j <= Len(s) }

CountInRange(s, v, a, b) ==
  Cardinality({ k \in a..b : s[k] = v })

Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values :
        CountInRange(s, v, 1, Len(s)) = CountInRange(t, v, 1, Len(t))

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Partition(old, new, i, j, p) ==
  /\ Len(old) = Len(new)
  /\ \A k \in 1..Len(old) :
        (k < i \/ k > j) => new[k] = old[k]
  /\ \A a \in i..p : \A b \in p+1..j : new[a] <= new[b]
  /\ \A v \in Values :
        CountInRange(old, v, i, j) = CountInRange(new, v, i, j)

\* ----------------------------------------------------------------------
\* Type correctness
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ \E s \in LimitedSeq(Values) :
        Len(s) > 0
        /\ seq = s
        /\ orig = s
        /\ work = { <<1, Len(s)>> }
        /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main iteration
Iter ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        LET i == I[1] IN
        LET j == I[2] IN
        IF i = j THEN
          /\ seq' = seq
          /\ work' = work \ {I}
          /\ UNCHANGED <<orig, pc>>
        ELSE
          /\ \E p \in i..j :
                /\ \E newSeq \in LimitedSeq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ Partition(seq, newSeq, i, j, p)
                      /\ seq' = newSeq
                      /\ let lower == IF i <= p-1 THEN { <<i, p-1>> } ELSE {} in
                         let upper == IF p+1 <= j THEN { <<p+1, j>> } ELSE {} in
                         work' = (work \ {I}) \cup lower \cup upper
                      /\ UNCHANGED <<orig, pc>>
          /\ UNCHANGED pc

\* ----------------------------------------------------------------------
\* Termination step
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
Next == Iter \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariant used for checking
Inv ==
  /\ TypeOK
  /\ \A I \in work : I \in Intervals(seq)
  /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness when algorithm finishes
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
Termination == <> (pc = "Done")

====