---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Operator that replaces Seq with a finite version for model checking
\* ----------------------------------------------------------------------
LimitedSeq(V, n) == { s \in Seq(V) : Len(s) <= n }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Intervals are represented as ordered pairs <<i,j>> with i <= j
\* ----------------------------------------------------------------------
Interval == <<i, j>> \in [i \in Nat, j \in Nat] : i # 0 /\ j # 0 /\ i <= j

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LenSeq == Len(seq)

\* Count of a value v in a sequence s
Count(v, s) == Cardinality({ k \in 1..Len(s) : s[k] = v })

\* Equality of multisets (permutation predicate)
IsPermutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(v, s1) = Count(v, s2)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences that could result from a correct
\* partition of seq on interval [i..j] with pivot p.
Partition(old, i, j, p) ==
  { new \in Seq(Values) :
      /\ Len(new) = Len(old)
      /\ \A k \in 1..Len(old) :
          IF (k < i) \/ (k > j) THEN new[k] = old[k] ELSE TRUE
      /\ \A a \in i..p :
           \A b \in p+1..j :
                new[a] <= new[b]
  }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ seq # <<>>                                   \* non‑empty
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "run"
     /\ work = {}
     /\ pc' = "done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "run"
     /\ work # {}
     /\ \E int \in work :
          LET i == int[1] IN
          LET j == int[2] IN
          IF i = j THEN
            /\ work' = work \ {int}
            /\ UNCHANGED <<seq, orig>>
            /\ pc' = "run"
          ELSE
            /\ \E p \in i..j :
                 /\ let lower  == IF p-1 >= i THEN <<i, p-1>> ELSE NULL in
                    let upper  == IF p+1 <= j THEN <<p+1, j>> ELSE NULL in
                    /\ work' = (work \ {int})
                         \cup (IF lower # NULL THEN {lower} ELSE {})
                         \cup (IF upper # NULL THEN {upper} ELSE {})
                    /\ \E newSeq \in Partition(seq, i, j, p) :
                         seq' = newSeq
                    /\ orig' = orig
                    /\ pc' = "run"
          )
  \/ /\ pc = "done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ \A int \in work :
        LET i == int[1] IN LET j == int[2] IN
        /\ i \in 1..Len(seq) /\ j \in i..Len(seq)
  /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Main invariant (permutation preservation and bounded work set)
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig)
  /\ \A int \in work :
        LET i == int[1] IN LET j == int[2] IN
        /\ i <= j

\* ----------------------------------------------------------------------
\* Partial correctness (when the algorithm terminates)
\* ----------------------------------------------------------------------
PCorrect ==
  pc = "done" => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\* Termination property (eventually the algorithm reaches the done state)
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect
THEOREM Spec => Termination

====