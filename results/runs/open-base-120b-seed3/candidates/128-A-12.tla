---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals, Integers

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* Finite version of Seq for model checking
\*-----------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES seq, origSeq, work, pc

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
Count(seq_, v_) == Cardinality({ i \in 1..Len(seq_) : seq_[i] = v_ })

IsPermutation(s1, s2) == \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Interval(i, j) == <<i, j>>

AddInterval(lo, hi) == IF lo <= hi THEN {<<lo, hi>>} ELSE {}

IndicesIn(I) == { k \in 1..Len(seq) : I[1] <= k /\ k <= I[2] }

PartitionSet(s, I, p) ==
  { s2 \in LimitedSeq :
      Len(s2) = Len(s) /\
      \A k \in 1..Len(s) :
        (k \notin IndicesIn(I) => s2[k] = s[k]) /\
      IsPermutation(s2, s) /\
      \A k \in IndicesIn(I) :
        (k <= p => s2[k] <= s2[p]) /\ (k > p => s2[k] >= s2[p])
  }

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq /\ Len(seq) > 0
  /\ origSeq = seq
  /\ work = { Interval(1, Len(seq)) }
  /\ pc = "Loop"

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          LET i == I[1] IN
          LET j == I[2] IN
          \/ /\ i = j
              /\ work' = work \ {I}
              /\ seq' = seq
              /\ origSeq' = origSeq
              /\ pc' = "Loop"
          \/ /\ i < j
              /\ \E p \in i..j :
                 /\ \E s2 \in PartitionSet(seq, I, p) :
                    /\ seq' = s2
                    /\ work' = (work \ {I})
                                 \cup AddInterval(i, p-1)
                                 \cup AddInterval(p+1, j)
                    /\ origSeq' = origSeq
                    /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, origSeq, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, origSeq, work, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ origSeq \in LimitedSeq
  /\ work \subseteq { Interval(i, j) :
                       i \in 1..Len(seq), j \in i..Len(seq) }
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, origSeq)
  /\ \A I \in work :
       LET i == I[1] IN LET j == I[2] IN
         i >= 1 /\ j <= Len(seq) /\ i <= j

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, origSeq))

\*-----------------------------------------------------------------
\* Liveness property
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* THE SPECIFICATION TO BE CHECKED
\*-----------------------------------------------------------------
\* The .cfg file will refer to the following identifiers:
\*   SPECIFICATION  -> Spec
\*   INVARIANTS     -> PCorrect, TypeOK, Inv
\*   PROPERTIES     -> Termination
\*   CONSTANTS      -> Values, MaxSeqLen
\*   LimitedSeq     -> defined above (replaces Seq)
\*-----------------------------------------------------------------
====