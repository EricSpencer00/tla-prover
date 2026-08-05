---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A bounded, finite version of `Seq` used by the .cfg's ValueBoundedSeq module.
LimitedSeq(n, A) == CHOOSE s \in Seq(A) : Len(s) = n /\ \A i \in 1..n : s[i] \in A

\* Permutations via automorphisms of the domain, used by the InvPermuted invariant.
Permutation(s) == { s \circ f : f \in {g \in [1..Len(s) -> 1..Len(s)] : \A i \in 1..Len(s) : \E j \in 1..Len(s) : g[i] = j /\ g[j] = i} }

\* The partition operator abstracts the act of rearranging one interval around a
\* pivot: it yields all permutations that leave the complement untouched while
\* placing the pivot's block between the low and high blocks.
Partition(s, i, j) == { u \in Permutation(s) :
                           \A k \in 1..Len(s) : (k < i \/ k >= j) => u[k] = s[k]
                           /\ \A k \in i..j-1 : \A l \in j..Len(s) : u[k] <= u[l] }

ASSUME Values \subseteq Int

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

INTERVALS == {i \in 1..Len(seq) : {j \in 1..Len(seq) : i <= j}}

TypeOK ==
  /\ seq \in LimitedSeq(MaxSeqLen, Values)
  /\ orig \in Permutation(seq)
  /\ work \subseteq INTERVALS
  /\ pc \in {"main"}

Init ==
  /\ \E s \in LimitedSeq(MaxSeqLen, Values) : seq = s
  /\ orig = seq
  /\ work = {INTERVALS}
  /\ pc = "main"

\* One iteration: pick an interval, partition it (or drop a singleton), and
\* replace it with its subintervals.
Step ==
  /\ pc = "main"
  /\ \E i \in work : /\ Len(i) = 2
                      /\ LET low == {k \in i[1]..i[2] : k < i[2]} /\ high == {k \in i[1]..i[2] : k >= i[2]}
                         IN \E s2 \in Partition(seq, i[1], i[2]) :
                              /\ seq' = s2
                              /\ work' = (work \ {i}) \cup {low, high}
  /\ pc' = pc
  /\ UNCHANGED orig

Terminate ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Step
  \/ Terminate
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* Termination: the algorithm always reaches its terminal state.
Termination == <>(pc = "done")

\* Partial correctness: if the algorithm has terminated, seq is a permutation
\* of orig and is sorted.
Sorted(s) == \A i \in 1..(Len(s) - 1) : s[i] <= s[i+1]
PCorrect == (pc = "done") => (seq \in Permutation(orig) /\ Sorted(seq))

\* The inductive invariant carried through the proof: each interval in work stays
\* sorted relative to the rest of the sequence, and permuting seq does not change
\* its multiset of values.
Inv ==
  /\ (\A i \in work : \A k \in i[1]..i[2] : \A l \in (INTERVALS \ work) : seq[k] <= seq[l])
  /\ Permutation(seq) = Permutation(orig)
  /\ work \subseteq INTERVALS

TypeOKInv == TypeOK /\ Inv
====