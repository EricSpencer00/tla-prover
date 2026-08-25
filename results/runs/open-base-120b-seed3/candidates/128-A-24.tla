---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT Values
CONSTANT MaxSeqLen

\* ----------------------------------------------------------------------
\* Operator that replaces Seq with a finite version for model checking
\* ----------------------------------------------------------------------
LimitedSeq(V, N) == { s \in Seq(V) : Len(s) <= N }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
\* An interval is a pair <<low, high>> with 1 <= low <= high <= Len(seq)
Interval == <<low: Nat, high: Nat>>  

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Indices(s) == 1 .. Len(s)

Count(v, s) == Cardinality({ i \in Indices(s) : s[i] = v })

IsPermutation(s1, s2) == 
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(v, s1) = Count(v, s2)

Sorted(s) == \A i, j \in Indices(s) : i < j => s[i] <= s[j]

\* Partition operator: returns the set of all sequences that could result
\* from a valid partition of interval <<i,j>> with pivot p.
Partition(old, <<i, j>>, p) ==
    { new \in Seq(Values) :
        /\ Len(new) = Len(old)
        /\ \A k \in Indices(old) :
              (k < i \/ k > j) => new[k] = old[k]
        /\ IsPermutation(SubSeq(old, i, j), SubSeq(new, i, j))
        /\ \A k \in i .. p : new[k] <= new[p]
        /\ \A k \in p+1 .. j : new[k] >= new[p]
    }

\* SubSeq extracts a contiguous subsequence; defined using Sequences' SubSeq
\* (which expects 1‑based indexing).  We reuse it directly.
\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \E s \in LimitedSeq(Values, MaxSeqLen) :
          Len(s) > 0
          /\ seq = s
          /\ orig = s
          /\ work = { <<1, Len(s)>> }
          /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
LoopStep ==
    /\ pc = "Loop"
    /\ work # {}
    /\ \E I \in work :
          LET i == I[1] IN
          LET j == I[2] IN
          IF i = j THEN
            /\ work' = work \ {I}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            /\ \E p \in i .. j :
                 /\ let newSeq == 
                       CHOOSE ns \in Partition(seq, I, p) : TRUE
                 in
                     /\ seq' = newSeq
                     /\ orig' = orig
                     /\ work' = (work \ {I}) \cup
                         { <<i, p-1>> } \cup { <<p+1, j>> }
                     /\ pc' = "Loop"
                     /\ \* remove possibly empty intervals
                     /\ work' = { I2 \in work' : I2[1] <= I2[2] }
          /\ pc' = "Loop"

DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work>>

Next == LoopStep \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<seq, orig, work, pc>>
Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in Seq(Values)
    /\ orig \in Seq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq { I \in Interval :
                        1 <= I[1] /\ I[1] <= I[2] /\ I[2] <= Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* General invariant (permutation preservation)
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ IsPermutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness invariant
\* ----------------------------------------------------------------------
PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Declared invariants and properties for the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == PCorrect, TypeOK, Inv
PROPERTIES == Termination

====