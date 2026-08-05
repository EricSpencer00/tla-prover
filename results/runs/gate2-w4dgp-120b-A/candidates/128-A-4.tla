---- MODULE Quicksort ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* This is a bounded rewrite of Sequences.Seq: it builds only sequences
\* up to a fixed maximum length, so the model stays finite.
LimitedSeq(f) == {s \in Seq(Values) : Len(s) <= MaxSeqLen /\ \A i \in DOMAIN s : s[i] = f[i]}
\* Permutations are defined as compositions with automorphisms, after
\* which the domain of the result is always the full domain of the input.
Automorphisms(S) == {f \in [S -> S] : \A a, b \in S : f[a] = f[b] => a = b}
Permutations(s) == {s \circ f : f \in Automorphisms(DOMAIN s)}
\* A partition over interval [a,b] around pivot c leaves everything
\* outside the interval untouched, and every element at or below the
\* pivot index is <= every element above it (the element-at-pivot itself
\* can be anywhere, which is what lets the permutation be nondeterministic).
Partitions(s, a, b, c) == {
  s2 \in Permutations(s) :
    \A i \in DOMAIN s2 :
      (i < a \/ i > b => s2[i] = s[i])
        /\ \A x \in a..c, y \in (c+1)..b : s2[x] <= s2[y]
}

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

Intervals == {i \in (Nat \times Nat) : i[1] <= i[2]}

TypeOK ==
  /\ seq \in Seq(Values)
  /\ original \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"run", "done"}

Init ==
  /\ \E s \in LimitedSeq([i \in 1..MaxSeqLen |-> CHOOSE c \in Values : TRUE]) :
       seq = s /\ original = s
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "run"

\* Intervals that partition the whole domain are not independent: the
\* contents of one can constrain the contents of another.  To reason about
\* each subproblem separately, the invariant records, at every moment,
\* which interval each index belongs to, and for each interval separately
\* records that its inside is sorted relative to its own outside.
DomainPartition ==
  (\E g \in [1..Len(seq) -> Intervals] :
     /\ \A i \in 1..Len(seq) : g[i] \in work \/ (i \in g[i] /\ Len(g[i]) > 1)
     /\ \A i, j \in 1..Len(seq) :
          (i < j /\ g[i] # g[j]) => g[i][2] < g[j][1] \/ g[j][2] < g[i][1])

PermutationPreserved == seq \in Permutations(original)
SortedWithinInterval ==
  \A i, j \in 1..Len(seq) : (\E I \in work : i \in I /\ j \in I /\ i < j) => seq[i] <= seq[j]

Inv == DomainPartition /\ PermutationPreserved /\ SortedWithinInterval

PartitionStep ==
  /\ pc = "run"
  /\ work # {}
  /\ \E I \in work : I[1] < I[2]
  /\ \E I \in work, c \in I[1]..I[2] :
       /\ \E s2 \in Partitions(seq, I[1], I[2], c) : seq' = s2
       /\ work' = (work \ {I}) \cup {<<I[1], c>>, <<c+1, I[2]>>}
  /\ pc' = "run"

Terminate ==
  /\ pc = "run"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stall == pc = "done" /\ UNCHANGED vars

Next == PartitionStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep) /\ WF_vars(Terminate)

PCorrect == (pc = "done") => (PermutationPreserved /\ SortedWithinInterval)

Termination == pc = "done"

====