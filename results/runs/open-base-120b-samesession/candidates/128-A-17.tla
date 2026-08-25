---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Intervals are represented as a two‑element tuple <<lo,hi>>
Intervals == { <<lo, hi>> : lo \in Nat, hi \in Nat, lo <= hi }

Low(iv) == iv[1]
High(iv) == iv[2]

\* Multiset of values of a sequence (or of a subsequence)
Bag(s) == [v \in Values |-> Cardinality({ i \in DOMAIN s : s[i] = v })]

BagSegment(s, lo, hi) ==
  [v \in Values |-> Cardinality({ i \in lo..hi : s[i] = v })]

Permutation(s1, s2) == Bag(s1) = Bag(s2)
PermutationSegment(s1, s2, lo, hi) == BagSegment(s1, lo, hi) = BagSegment(s2, lo, hi)

IsSorted(s) == \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* Partition predicate for a chosen pivot index p inside interval iv
Partition(old, new, iv, p) ==
  LET lo == Low(iv) IN
  LET hi == High(iv) IN
    /\ new \in LimitedSeq(Values) /\ Len(new) = Len(old)
    /\ \A j \in DOMAIN old : (j < lo \/ j > hi) => new[j] = old[j]
    /\ PermutationSegment(old, new, lo, hi)
    /\ \A j \in lo..p : \A k \in p+1..hi : new[j] <= new[k]

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ---------- Initial state ----------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ---------- Next state ----------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E iv \in work :
          LET lo == Low(iv) IN
          LET hi == High(iv) IN
            IF lo = hi THEN
              /\ seq' = seq
              /\ work' = work \ {iv}
            ELSE
              /\ \E p \in lo..hi :
                    /\ Partition(seq, seq', iv, p)
                    /\ work' = (work \ {iv}) \cup
                        (IF lo <= p-1 THEN { <<lo, p-1>> } ELSE {}) \cup
                        (IF p+1 <= hi THEN { <<p+1, hi>> } ELSE {})
            /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ seq' = seq
     /\ work' = work
     /\ pc' = "Done"
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ---------- Specification ----------
Spec == Init /\ [] [Next]_vars

\* ---------- Invariants ----------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq Intervals
  /\ \A iv \in work : Low(iv) \in 1..Len(seq) /\ High(iv) \in 1..Len(seq) /\ Low(iv) <= High(iv)
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ Permutation(seq, orig)

PCorrect ==
  /\ pc = "Done"
  => /\ IsSorted(seq)
     /\ Permutation(seq, orig)

\* ---------- Property ----------
Termination == <> (pc = "Done")

\* ---------- Declared identifiers for the .cfg ----------
\* (the names below are required by the configuration file)
\* CONSTANTS: Values, MaxSeqLen
\* SPECIFICATION formula: Spec
\* INVARIANTS: PCorrect, TypeOK, Inv
\* PROPERTIES: Termination
\* LimitedSeq is defined above and replaces Seq from Sequences

====