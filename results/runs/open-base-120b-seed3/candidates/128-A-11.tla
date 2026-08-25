---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Operator that limits the length of sequences (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(i) == i \in Nat
Interval == <<Nat, Nat>>

\* The set of all well‑formed intervals for the current sequence length.
Intervals == { <<i, j>> : i \in 1..Len(seq) /\ j \in i..Len(seq) }

\* Permutation predicate (there exists a bijection between positions)
Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \E f \in [1..Len(s) -> 1..Len(t)] :
        ( \A i \in 1..Len(s) : s[i] = t[f[i]] )
        /\ ( \A i, j \in 1..Len(s) : f[i] = f[j] => i = j )

\* Sorted predicate (non‑decreasing order)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all possible results of a valid partition step
Partition(old, i, j, p) ==
  { new \in Seq(Values) :
        /\ Len(new) = Len(old)
        /\ ( \A k \in 1..Len(old) :
               IF k \notin i..j THEN new[k] = old[k] ELSE TRUE )
        /\ ( \A a \in i..p : \A b \in p+1..j : new[a] <= new[b] )
        /\ Permutation(new, old) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Main transition relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ work # {}
     /\ \E I \in work :
          LET i == I[1] IN j == I[2] IN
            IF i = j THEN
               /\ seq' = seq
               /\ work' = work \ {I}
               /\ pc' = "Run"
            ELSE
               /\ \E p \in i..j :
                     \E newSeq \in Partition(seq, i, j, p) :
                       /\ seq' = newSeq
                       /\ work' = (work \ {I})
                                 \cup (IF i <= p-1 THEN {<<i, p-1>>} ELSE {})
                                 \cup (IF p+1 <= j THEN {<<p+1, j>>} ELSE {})
                       /\ pc' = "Run"
  \/ /\ pc = "Run"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Inductive invariant (type + permutation preservation)
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, the result is sorted and a
\* permutation of the original input.
\* ----------------------------------------------------------------------
PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers for the .cfg file
\* ----------------------------------------------------------------------
\* (the names are required exactly as listed)
\* SPECIFICATION  == Spec
\* INVARIANTS      == PCorrect, TypeOK, Inv
\* PROPERTIES      == Termination

====