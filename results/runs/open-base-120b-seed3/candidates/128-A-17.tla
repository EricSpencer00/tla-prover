---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Operator that limits Seq to sequences of bounded length
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
INTERVAL == [lo : Nat, hi : Nat]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Interval constructor
Interval(lo, hi) == [lo |-> lo, hi |-> hi]

\* All intervals that are well‑formed with respect to the current sequence
Intervals == { I \in INTERVAL : I.lo <= I.hi /\ I.hi <= Len(seq) }

\* Injectivity of a function
Injective(f) == \A i, j \in DOMAIN f : f[i] = f[j] => i = j

\* Permutation of two sequences (same multiset of values)
Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \E f \in [1..Len(s1) -> 1..Len(s2)] :
        /\ Injective(f)
        /\ \A i \in 1..Len(s1) : s1[i] = s2[f[i]]

\* Sortedness (non‑decreasing)
IsSorted(s) == \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* Count occurrences of a value v inside interval I of a sequence s
CountInInterval(s, I, v) ==
  Cardinality({ i \in I.lo..I.hi : s[i] = v })

\* Partition relation for a chosen interval I and pivot p
Partition(old, I, p, new) ==
  /\ Len(old) = Len(new)
  /\ \A j \in 1..Len(old) :
        (j < I.lo \/ j > I.hi) => new[j] = old[j]
  /\ \A i \in I.lo..p : \A j \in p+1..I.hi : new[i] <= new[j]
  /\ \A v \in Values :
        CountInInterval(old, I, v) = CountInInterval(new, I, v)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Inductive invariant (here we keep it simple; a stronger invariant can be added)
\* ----------------------------------------------------------------------
Inv == TypeOK

\* ----------------------------------------------------------------------
\* Partial‑correctness property
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Termination (liveness) property
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { Interval(1, Len(seq)) }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
\* 1. Remove a singleton interval
SingletonStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        I.lo = I.hi
        /\ UNCHANGED <<seq, orig>>
        /\ work' = work \ {I}
        /\ pc' = pc

\* 2. Partition a non‑singleton interval
PartitionStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        I.lo < I.hi
        /\ \E p \in I.lo..I.hi :
              /\ \E newSeq \in Seq(Values) :
                    /\ Len(newSeq) = Len(seq)
                    /\ Partition(seq, I, p, newSeq)
                    /\ LET lower == IF p > I.lo THEN { Interval(I.lo, p-1) } ELSE {}
                       upper == IF p < I.hi THEN { Interval(p+1, I.hi) } ELSE {}
                    IN
                       /\ seq' = newSeq
                       /\ orig' = orig
                       /\ work' = (work \ {I}) \union lower \union upper
                       /\ pc' = pc

\* 3. No more work – terminate
TerminateStep ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* 4. Stuttering after termination
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ SingletonStep
  \/ PartitionStep
  \/ TerminateStep
  \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Declared identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* (already defined above)
\*   CONSTANTS: Values, MaxSeqLen
\*   SPECIFICATION: Spec
\*   INVARIANTS: PCorrect, TypeOK, Inv
\*   PROPERTIES: Termination
\*   LimitedSeq – defined above
====