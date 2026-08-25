---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
\* Bounded version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen /\ Len(s) > 0 }

\* Intervals are pairs <<i,j>> with 1 <= i <= j <= Len(seq)
Interval(i, j) == <<i, j>>

Intervals(seq) == { <<i, j>> \in Nat \X Nat :
                    1 <= i /\ i <= j /\ j <= Len(seq) }

\* Count of a value v in a sequence
Count(s, v) == Cardinality({ k \in 1..Len(s) : s[k] = v })

\* Permutation predicate
Permutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(s1, v) = Count(s2, v)

\* Sortedness predicate (non‑decreasing)
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences obtainable by a valid partition of
\* interval I = <<i,j>> with pivot p (i <= p <= j)
Partition(seq, I, p) ==
  LET i == I[1] IN
  LET j == I[2] IN
  { s \in Seq(Values) :
        /\ Len(s) = Len(seq)
        /\ \A k \in 1..Len(seq) :
              (k < i \/ k > j) => s[k] = seq[k]
        /\ \A v \in Values :
              Count({k \in i..j}, v, s) = Count({k \in i..j}, v, seq)
        /\ \A k \in i..p : s[k] <= s[p]
        /\ \A k \in p+1..j : s[k] >= s[p] }

\* Helper for counting inside a subrange
Count(Range, v, s) ==
  Cardinality({ k \in Range : s[k] = v })

\* ---------- Variables ----------
VARIABLES seq, orig, workset, pc

\* ---------- Initial state ----------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ workset = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ---------- Actions ----------
RunStep ==
  /\ pc = "Run"
  /\ workset # {}
  /\ \E I \in workset :
        LET i == I[1] IN
        LET j == I[2] IN
        IF i = j THEN
          /\ (* singleton interval: just remove it *)
             workset' = workset \ {I}
          /\ seq' = seq
          /\ orig' = orig
          /\ pc' = "Run"
        ELSE
          /\ \E p \in i..j :
                /\ seq' \in Partition(seq, I, p)
                /\ workset' = (workset \ {I})
                              \cup (IF i <= p-1 THEN { <<i, p-1>> } ELSE {})
                              \cup (IF p+1 <= j THEN { <<p+1, j>> } ELSE {})
                /\ orig' = orig
                /\ pc' = "Run"

TerminateStep ==
  /\ pc = "Run"
  /\ workset = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, workset>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, workset, pc>>

Next ==
  \/ RunStep
  \/ TerminateStep
  \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<seq, orig, workset, pc>>

\* ---------- Invariants ----------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ workset \subseteq Intervals(seq)
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)

PCorrect ==
  (pc = "Done") => (Permutation(seq, orig) /\ Sorted(seq))

\* ---------- Property ----------
Termination == <> (pc = "Done")

\* ---------- The required names for the .cfg ----------
SPECIFICATION == Spec
INVARIANTS == PCorrect, TypeOK, Inv
PROPERTIES == Termination

====