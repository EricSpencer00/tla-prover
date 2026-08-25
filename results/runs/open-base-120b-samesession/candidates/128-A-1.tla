---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS Values, MaxSeqLen

\*--- Operator replacing Seq with a bounded version ---------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*--- Variables --------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\*--- Helper definitions -----------------------------------------------------------
Interval == <<i, j>> \* a pair of indices with i <= j

Intervals == { I \in Seq(1..Len(seq)) :
                /\ Len(I) = 2
                /\ LET i == I[1], j == I[2] IN i \in 1..Len(seq) /\ j \in i..Len(seq) }

CountIn(s, v, a, b) == { k \in a..b : s[k] = v }

Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values :
        Cardinality(CountIn(s, v, 1, Len(s))) =
        Cardinality(CountIn(t, v, 1, Len(t)))

Sorted(s) ==
  /\ Len(s) >= 0
  /\ \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\*--- Partition operator (nondeterministic set of valid results) --------------------
Partition(old, i, j, p) ==
  { new \in LimitedSeq(Values) :
        /\ Len(new) = Len(old)
        /\ \A k \in 1..Len(old) :
              (k < i \/ k > j) => new[k] = old[k]
        /\ \A a \in i..p : \A b \in p+1..j : new[a] <= new[b]
        /\ \A v \in Values :
              Cardinality(CountIn(new, v, i, j)) =
              Cardinality(CountIn(old, v, i, j)) }

\*--- Initial state ---------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\*--- Next-state relation ---------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          LET i == I[1], j == I[2] IN
          IF i = j THEN
            /\ seq' = seq
            /\ orig' = orig
            /\ work' = work \ {I}
            /\ pc' = "Loop"
          ELSE
            /\ \E p \in i..j :
                 /\ \E newSeq \in Partition(seq, i, j, p) :
                       seq' = newSeq
                 /\ orig' = orig
                 /\ work' = (work \ {I}) \cup { <<i, p-1>>, <<p+1, j>> }
                 /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\*--- Specification ----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--- Type correctness invariant --------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals

\*--- Main invariant (can be strengthened later) ---------------------------------
Inv == TypeOK

\*--- Partial correctness when algorithm finishes ---------------------------------
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\*--- Liveness property: eventual termination --------------------------------------
Termination == <> (pc = "Done")

=============================================================================