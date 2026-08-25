---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(s, x) == Cardinality({ i \in 1..Len(s) : s[i] = x })

IsPermutation(s, t) == 
    /\ Len(s) = Len(t)
    /\ \A x \in Values : Count(s, x) = Count(t, x)

Sorted(s) == 
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* An interval is a pair <<i, j>> with 1 ≤ i ≤ j ≤ Len(seq)
Interval == [i : Nat, j : Nat]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ seq \in LimitedSeq(Values)
    /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Partition predicate (abstract)
\* ----------------------------------------------------------------------
Partition(old, i, j, p, new) == 
    /\ Len(old) = Len(new)
    /\ \A k \in 1..Len(old) : 
          IF (k < i) \/ (k > j) THEN new[k] = old[k] ELSE TRUE
    /\ \A a \in i..p : \A b \in p+1..j : new[a] <= new[b]
    /\ IsPermutation(old, new)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Single == 
    /\ pc = "Loop"
    /\ work # {}
    /\ \E I \in work : 
          LET i == I[1] IN 
          LET j == I[2] IN 
          i = j
    /\ \E I \in work : 
          LET i == I[1] IN 
          LET j == I[2] IN 
          i = j
    /\ UNCHANGED <<seq, orig>>
    /\ work' = work \ { I }
    /\ pc' = "Loop"

PartitionAction == 
    /\ pc = "Loop"
    /\ work # {}
    /\ \E I \in work : 
          LET i == I[1] IN 
          LET j == I[2] IN 
          i < j
    /\ \E I \in work : 
          LET i == I[1] IN 
          LET j == I[2] IN 
          i < j
    /\ \E p \in i..j :
          \E newSeq \in LimitedSeq(Values) :
              /\ Len(newSeq) = Len(seq)
              /\ Partition(seq, i, j, p, newSeq)
              /\ seq' = newSeq
              /\ orig' = orig
              /\ work' = (work \ { I })
                         \cup (IF i <= p-1 THEN { <<i, p-1>> } ELSE {})
                         \cup (IF p+1 <= j THEN { <<p+1, j>> } ELSE {})
              /\ pc' = "Loop"

Terminate == 
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

Stutter == 
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == 
    \/ Single
    \/ PartitionAction
    \/ Terminate
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
PCorrect == 
    /\ pc = "Done"
    => /\ IsPermutation(seq, orig)
       /\ Sorted(seq)

Inv == 
    /\ TypeOK
    /\ (pc = "Loop" => work # {} \/ work = {})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================